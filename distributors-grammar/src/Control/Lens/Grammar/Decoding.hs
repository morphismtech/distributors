{- |
Module      : Control.Lens.Grammar.Decoding
Description : grammar-constrained decoding of next-piece predictors
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable

A language model generates text a piece at a time: given the pieces
so far, it weighs each piece of its vocabulary, & ending, & a decoder
chooses one. Grammar-constrained decoding masks those weights, so that
only pieces which continue a word of a grammar's language may be
chosen, & ending only at a word of the language, so the generated text
always parses. See Willard & Louf,
[Efficient Guided Generation for Large Language Models]
(https://arxiv.org/abs/2307.09702).

A `Grammar` is a decoder's constraint, as it's a parser, & a printer,
& a t'Transducer', by `transducerG`, whose t'Chart's are the states of
the constraint, scanned a token at a time. `decodeG` decodes a syntax
value, parsing the text which it masks its predictor to generate.

==== Pieces & tokens

A language model's vocabulary is not its grammar's tokens: models
generate pieces of text, by sub-word tokenizers such as byte-pair
encoding, each piece a string of many characters, which needn't align
with a grammar's lexemes. A t'Vocabulary' is the strings of tokens
which its pieces stand for, indexed by position, as a model indexes its
vocabulary, & a piece is allowed where a t'Chart' scans its whole
string. Masking a vocabulary is thus composing a grammar with the
detokenizer, the monoid homomorphism from strings of pieces to strings
of tokens, whose inverse image of a context-free language is
context-free. See Koo, Liu & He,
[Automata-based constraints for language model decoding]
(https://arxiv.org/abs/2407.08103).

`allowedPieces` scans a vocabulary's pieces together, by a trie, so
pieces which share a prefix share its scanning, & a prefix which is a
dead end prunes every piece which begins with it.

Many strings of pieces stand for the same text, but a model is trained
on only one of them, its tokenizer's canonical one, & weighs the others
poorly. A mask allows them all, which can steer a model to text it
would've tokenized differently. See Beurer-Kellner, Fischer & Vechev,
[Guiding LLMs The Right Way: Fast, Non-Invasive Constrained Generation]
(https://arxiv.org/abs/2403.06988), & Vieira et al.,
[From Language Models over Tokens to Language Models over Characters]
(https://arxiv.org/abs/2412.03719).

==== Opportunistic masking

Masking a whole vocabulary each step costs a scan of its trie, while
a model usually weighs most what the grammar allows anyway. So `decode`
first lets its t'Chooser' choose from the unmasked weights, & only
masks when the choice isn't allowed, choosing again from the masked
weights. This decodes exactly as masking each step would: a `greedy`
choice which is allowed is the masked weights' greatest; & a `sampled`
choice is sampled from the masked weights, as a piece @i@ of weight
@p_i@, out of an allowed total of @Z@, is chosen first with
probability @p_i@, & else, with probability @1 - Z@, then with
@p_i / Z@, in all @p_i / Z@.

==== Masking is not conditioning

Masking a model's weights a piece at a time decodes from a different
distribution than the model's, conditioned on generating a word of the
language: masking can't see that an allowed piece leads only to words
the model weighs poorly. Decoding from the conditional distribution
is intractable in general, & approximated by importance sampling &
sequential Monte Carlo. See Park et al., [Grammar-Aligned Decoding]
(https://arxiv.org/abs/2405.21047), & Loula et al.,
[Syntactic and Semantic Control of Large Language Models via Sequential Monte Carlo]
(https://arxiv.org/abs/2504.13139).

==== Predictors

A t'Predictor' is any function from the pieces so far to t'Weights',
in a monad, so a language model is wrapped as a predictor by calling
it, in `IO`, & keeping its prompt in a closure; its logits @l_i@ are
weights @exp l_i@, & its end-of-sequence piece is `endWeight`.
-}

module Control.Lens.Grammar.Decoding
  ( -- * Decoding
    decodeG
  , decode
  , Decoded (..)
    -- * Predictors
  , Predictor
  , Weights (..)
    -- * Choosers
  , Chooser
  , greedy
  , sampled
    -- * Vocabularies
  , Vocabulary
  , vocabulary
  , vocabularyPiece
  , vocabularySize
  , allowedPieces
  ) where

import Control.Lens.Grammar
import Control.Monad.State (StateT, state)
import qualified Data.IntMap.Lazy as LazyIntMap
import qualified Data.IntMap.Strict as IntMap
import Data.IntMap.Strict (IntMap)
import qualified Data.IntSet as IntSet
import Data.IntSet (IntSet)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Maybe (fromMaybe)
import System.Random (RandomGen, randomR)

-- $setup
-- >>> import Control.Lens (only)
-- >>> import Control.Lens.Grammar
-- >>> import Control.Monad.State (evalStateT)
-- >>> import Data.Functor.Identity (runIdentity)
-- >>> import qualified Data.IntMap.Strict as IntMap
-- >>> import System.Random (mkStdGen)
-- >>> :{
-- let boolG :: Grammar Char Bool
--     boolG = orP [only True >? terminal "true", only False >? terminal "false"]
-- :}

{- | The weights a t'Predictor' puts on its next choice:
on each piece of its t'Vocabulary', by index, & on ending.
Weights are nonnegative & needn't sum to one; a piece missing
from `pieceWeights` has no weight.
-}
data Weights = Weights
  { pieceWeights :: IntMap Double
  , endWeight :: Double
  } deriving stock (Eq, Show)

{- | A next-piece predictor, which weighs what comes next,
given the indices of the pieces so far.
-}
type Predictor m = [Int] -> m Weights

{- | A decoder's choice, among t'Weights', of the index of a piece,
or `Nothing`, to end. A t'Chooser' should only choose what has weight.
-}
type Chooser m = Weights -> m (Maybe Int)

{- | The text a decoder generates, by how it stopped. -}
data Decoded token
  = Finished [token]
  -- ^ chosen to end, at a word of the language
  | Stuck [token]
  -- ^ nothing allowed next has weight
  | Truncated [token]
  -- ^ out of pieces, at the bound on how many to generate
  deriving stock (Eq, Ord, Show, Read)

{- | Choose what weighs most, preferring to end,
& the least index of the pieces which weigh most.

>>> runIdentity (greedy (Weights (IntMap.fromList [(0, 1), (1, 3), (2, 3)]) 2))
Just 1
-}
greedy :: Applicative m => Chooser m
greedy (Weights pieces end) = pure (IntMap.foldlWithKey' heavier Nothing pieces')
  where
    pieces' = IntMap.filter (> max 0 end) pieces
    heavier best i w = case best of
      Just j | pieces' IntMap.! j >= w -> best
      _ -> Just i

{- | Sample in proportion to weight, by a random generator.

>>> let weights = Weights (IntMap.fromList [(0, 1), (1, 1)]) 0
>>> evalStateT (traverse (const (sampled weights)) [1 .. 8 :: Int]) (mkStdGen 7)
[Just 0,Just 1,Just 0,Just 1,Just 0,Just 0,Just 0,Just 1]
-}
sampled :: (RandomGen g, Monad m) => Chooser (StateT g m)
sampled (Weights pieces end) = do
  r <- state (randomR (0, total))
  pure (pick r)
  where
    end' = max 0 end
    pieces' = IntMap.toList (IntMap.filter (> 0) pieces)
    total = end' + sum (map snd pieces')
    pick r
      | r < end' || null pieces' = Nothing
      | otherwise = go (r - end') pieces'
    go _ [(i, _)] = Just i
    go r ((i, w) : rest)
      | r < w = Just i
      | otherwise = go (r - w) rest
    go _ [] = Nothing

{- | A language model's vocabulary, as the strings of tokens its pieces
stand for, indexed by their positions in the list `vocabulary` is given,
from @0@. The empty piece, which would generate nothing, is never allowed.
-}
data Vocabulary token = Vocabulary
  { vocabularyPieces :: IntMap [token]
  , vocabularyTrie :: Trie token
  }

-- A trie of a vocabulary's pieces, by their tokens,
-- with the indices of the pieces which end at each node.
data Trie token = Trie IntSet (Map token (Trie token))

{- | A t'Vocabulary' of pieces, indexed by position. -}
vocabulary :: Ord token => [[token]] -> Vocabulary token
vocabulary pieces = Vocabulary
  { vocabularyPieces = IntMap.fromList indexed
  , vocabularyTrie = foldl' insert (Trie IntSet.empty Map.empty) indexed
  }
  where
    indexed = [(i, piece) | (i, piece) <- zip [0 ..] pieces, not (null piece)]
    insert (Trie ends next) (i, piece) = case piece of
      [] -> Trie (IntSet.insert i ends) next
      x : xs -> Trie ends (Map.alter (Just . grow) x next)
        where grow sub = insert (fromMaybe (Trie IntSet.empty Map.empty) sub) (i, xs)

{- | The string of tokens a piece stands for, by index. -}
vocabularyPiece :: Vocabulary token -> Int -> Maybe [token]
vocabularyPiece vocab i = IntMap.lookup i (vocabularyPieces vocab)

{- | The number of nonempty pieces in a t'Vocabulary'. -}
vocabularySize :: Vocabulary token -> Int
vocabularySize = IntMap.size . vocabularyPieces

{- | The pieces of a t'Vocabulary' which a t'Chart' scans, by index,
with the t'Chart' after each.

>>> let vocab = vocabulary ["t", "tr", "true", "fa", "false", "lse", "x"]
>>> let et = transducerG @Char boolG
>>> IntMap.keys (allowedPieces vocab (startChart et))
[0,1,2,3,4]
>>> IntMap.keys <$> (allowedPieces vocab <$> scanChartMany "fa" (startChart et))
Just [5]
-}
allowedPieces
  :: Categorized token
  => Vocabulary token -> Chart token -> IntMap (Chart token)
allowedPieces vocab chart0 = fst (walk (vocabularyTrie vocab) 0 (IntMap.empty, memo0))
  where
    memo0 = Memo (IntMap.singleton 0 chart0) IntMap.empty Map.empty

    walk (Trie _ next) chartId accMemo = Map.foldlWithKey' step accMemo next
      where
        step (acc, memo) x sub@(Trie ends next') = case scanned chartId x memo of
          (Nothing, memo') -> acc `seq` (acc, memo')
          (Just (chartId', chart'), memo') ->
            let acc' = IntSet.foldl' (\m i -> IntMap.insert i chart' m) acc ends
            in if Map.null next'
              then acc' `seq` (acc', memo')
              else walk sub chartId' (acc', memo')

    -- the chart a chart is scanned to by a token, remembered by token,
    -- & numbered by scan, so tokens which scan a chart alike share it
    scanned chartId x memo = case Map.lookup x table of
      Just next -> (next, memo)
      Nothing -> (next, memo'
        { memoNext = IntMap.insert chartId (Map.insert x next table) (memoNext memo') })
        where
          chart = memoCharts memo IntMap.! chartId
          scan = chartScan x chart
          (next, memo')
            | nullScan scan = (Nothing, memo)
            | otherwise = case Map.lookup (chartId, scan) (memoScanned memo) of
                Just chartId' -> (Just (chartId', memoCharts memo IntMap.! chartId'), memo)
                Nothing ->
                  let
                    chartId' = IntMap.size (memoCharts memo)
                    chart' = fromMaybe (error "allowedPieces: an empty scan")
                      (scanChartBy scan chart)
                  in
                    ( Just (chartId', chart')
                    , memo
                      { memoCharts = LazyIntMap.insert chartId' chart' (memoCharts memo)
                      , memoScanned = Map.insert (chartId, scan) chartId' (memoScanned memo)
                      }
                    )
      where
        table = IntMap.findWithDefault Map.empty chartId (memoNext memo)

-- The charts `allowedPieces` reaches, numbered: tokens which scan
-- a chart alike reach the same chart, which is scanned & closed once.
data Memo token = Memo
  { memoCharts :: IntMap (Chart token)
  -- ^ lazily, so a chart's only closed once a piece is scanned from it
  , memoNext :: IntMap (Map token (Maybe (Int, Chart token)))
  -- ^ the chart, & its number, a chart is scanned to by a token,
  -- by the chart's number
  , memoScanned :: Map (Int, Scan) Int
  -- ^ the number of the chart a chart is scanned to by a scan
  }

{- | Decode text of a t'Transducer''s language, from a t'Predictor',
by a t'Chooser', in at most a given number of pieces.
Each step, the predictor weighs the pieces of a t'Vocabulary', &
ending; the chooser chooses among them, masked to what the grammar
allows; & a chosen piece is scanned, by the t'Chart' of the text so far.

>>> let vocab = vocabulary ["tr", "ue", "true", "false", "f"]
>>> let et = transducerG @Char boolG
>>> let uniform _ = pure (Weights (IntMap.fromList [(i, 1) | i <- [0 .. 4]]) 1)
>>> runIdentity (decode greedy uniform vocab 10 et)
Finished "true"
>>> evalStateT (decode sampled uniform vocab 10 et) (mkStdGen 1)
Finished "false"

A predictor which only ever weighs ending, outside the language, is stuck.

>>> runIdentity (decode greedy (\_ -> pure (Weights IntMap.empty 1)) vocab 10 et)
Stuck ""
-}
decode
  :: (Categorized token, Monad m)
  => Chooser m
  -> Predictor m
  -> Vocabulary token
  -> Int {- ^ the most pieces to generate -}
  -> Transducer token
  -> m (Decoded token)
decode choose predict vocab bound et = go 0 [] [] (startChart et)
  where
    go n pieces chunks chart
      | n >= bound = pure (Truncated text)
      | otherwise = do
          weights <- predict (reverse pieces)
          choice <- choose weights
          case choice of
            Nothing | chartAccepts chart, endWeight weights > 0 -> pure (Finished text)
            Just i
              | Just piece <- vocabularyPiece vocab i
              , Just chart' <- scanChartMany piece chart ->
                  go (n + 1) (i : pieces) (piece : chunks) chart'
            -- the unmasked choice isn't allowed, so mask & choose again
            _ -> do
              let
                allowed = allowedPieces vocab chart
                masked = Weights
                  { pieceWeights = IntMap.filter (> 0)
                      (IntMap.intersectionWith const (pieceWeights weights) allowed)
                  , endWeight = if chartAccepts chart then max 0 (endWeight weights) else 0
                  }
              if IntMap.null (pieceWeights masked) && endWeight masked <= 0
                then pure (Stuck text)
                else do
                  choice' <- choose masked
                  case choice' of
                    Nothing | endWeight masked > 0 -> pure (Finished text)
                    Just i
                      | Just chart' <- IntMap.lookup i allowed
                      , Just piece <- vocabularyPiece vocab i ->
                          go (n + 1) (i : pieces) (piece : chunks) chart'
                    _ -> pure (Stuck text)
      where
        text = concat (reverse chunks)

{- | Decode a syntax value of a `Grammar`, from a t'Predictor',
by a t'Chooser', in at most a given number of pieces, parsing
the text it decodes, or returning it, unless it `Finished`.

>>> let vocab = vocabulary ["tr", "ue", "true", "false", "f"]
>>> let uniform _ = pure (Weights (IntMap.fromList [(i, 1) | i <- [0 .. 4]]) 1)
>>> runIdentity (decodeG greedy uniform vocab 10 boolG)
Right True
-}
decodeG
  :: (Categorized token, Monad m)
  => Chooser m
  -> Predictor m
  -> Vocabulary token
  -> Int {- ^ the most pieces to generate -}
  -> Grammar token a
  -> m (Either (Decoded token) a)
decodeG choose predict vocab bound grammar = do
  decoded <- decode choose predict vocab bound (transducerG grammar)
  pure $ case decoded of
    Finished word | (a, []) : _ <- parseG grammar word -> Right a
    _ -> Left decoded
