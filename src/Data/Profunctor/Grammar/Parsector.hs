{-|
Module      : Data.Profunctor.Grammar.Parsector
Description : lookahead grammar distributor
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Data.Profunctor.Grammar.Parsector
  ( -- * Parsector
    Parsector (..)
  , ParsecState (..)
  , ParsecError (..)
  , parsecP
  , unparsecP
  ) where

import Control.Applicative
import Control.Arrow
import Control.Category
import Data.Function hiding (id, (.))
import Control.Lens
import Control.Lens.Grammar.BackusNaur
import Control.Lens.Grammar.Boole
import Control.Lens.Grammar.Kleene
import Control.Lens.Grammar.Symbol
import Control.Lens.Grammar.Token
import Control.Lens.PartialIso
import Control.Monad
import Control.Monad.Fail.Try
import Data.Profunctor
import Data.Profunctor.Distributor
import Data.Profunctor.Filtrator
import Data.Profunctor.Monoidal
import Data.Tree
import GHC.Exts
import Prelude hiding (id, (.))
import Witherable

{- | `Parsector` is an invertible parser which can be used
to parse with `parsecP` or print with `unparsecP`,
yielding a `ParsecState`, with detailed errors and offset tracking.

`(<|>)` uses left-biased ordered choice in both parse and print mode:
if the left alternative succeeds it is committed to immediately,
regardless of mode or how much input was consumed.
On any failure the right alternative is always tried.
Errors at the same offset are merged.

`optionP` is mode-sensitive: in parse mode it tries @p@ first
(greedy), falling back to the default; in print mode it tries
the default first so that a value matching the default prism
short-circuits without entering @p@.
-}
newtype Parsector s a b = Parsector
  { runParsector :: forall x. (ParsecState s b -> x) -> ParsecState s a -> x }

{- | `ParsecError` is the error payload inside a failed `ParsecState`.
-}
data ParsecError s = ParsecError
  { parsecExpect :: TokenClass (Item s)
    -- ^ class of expected token `Item`s at the failure offset
  , parsecLabels :: [Tree String]
    {- ^ forest of `rule` labels active at failure;
    nested @`rule`@ calls build children, @('<|>')@ merges siblings.
    -}
  }
deriving stock instance
  ( Categorized (Item s)
  , Show (Item s), Show (Categorize (Item s))
  ) => Show (ParsecError s)
deriving stock instance
  ( Categorized (Item s)
  , Read (Item s), Read (Categorize (Item s))
  ) => Read (ParsecError s)
deriving stock instance Categorized (Item s) => Eq (ParsecError s)
deriving stock instance Categorized (Item s) => Ord (ParsecError s)
instance Categorized (Item s) => Semigroup (ParsecError s) where
  ParsecError e1 l1 <> ParsecError e2 l2 = ParsecError (e1 >||< e2) (l1 ++ l2)
instance Categorized (Item s) => Monoid (ParsecError s) where
  mempty = ParsecError falseB []

{- | `ParsecState` is the outpute type for `parsecP` & `unparsecP`.
It's the fundamental building block of `Parsector`.
@Parsector s a b@ is equivalent to
@ParsecState s a -> ParsecState s b@, so it has a dual
interpretation as input and output.
-}
data ParsecState s a = ParsecState
  { parsecOffset :: !Word
    -- ^ number of tokens either parsed or printed
  , parsecStream :: s -- ^ input and output stream
  , parsecResult :: Either (ParsecError s) a
    {- ^ As an input @parsecResult@ represents either parse mode,
    `Left` `mempty`, or print mode with an input syntax value.
    As an output @parsecResult@ represents either an error or
    a successful result with an output syntax value.
    -}
  } deriving (Functor, Foldable, Traversable)
deriving stock instance
  ( Categorized (Item s)
  , Show (Item s), Show (Categorize (Item s))
  , Show a, Show s
  ) => Show (ParsecState s a)
deriving stock instance
  ( Categorized (Item s)
  , Read (Item s), Read (Categorize (Item s))
  , Read a, Read s
  ) => Read (ParsecState s a)
deriving stock instance
  ( Categorized (Item s)
  , Eq a, Eq s
  ) => Eq (ParsecState s a)
deriving stock instance
  ( Categorized (Item s)
  , Ord a, Ord s
  ) => Ord (ParsecState s a)

-- | `Parsector` is parsed using `parsecP`.
parsecP :: Categorized (Item s) => Parsector s a b -> s -> ParsecState s b
parsecP p s = runParsector p id (ParsecState 0 s (Left mempty))

-- | `Parsector` is printed using `unparsecP`.
unparsecP :: Parsector s a b -> a -> s -> ParsecState s b
unparsecP p a s = runParsector p id (ParsecState 0 s (Right a))

-- Parsector instances
instance
  ( Categorized token, Item s ~ token
  , Cons s s token token, Snoc s s token token
  ) => Tokenized token (Parsector s token token) where
  anyToken = tokenClass anyToken
  token t = tokenClass (token t)
  oneOf ts = tokenClass (oneOf ts)
  notOneOf ts = tokenClass (notOneOf ts)
  asIn cat = tokenClass (asIn cat)
  notAsIn cat = tokenClass (notAsIn cat)
instance
  ( Categorized token, Item s ~ token
  , Cons s s token token, Snoc s s token token
  ) => TokenAlgebra token (Parsector s token token) where
    tokenClass test = Parsector $ \callback query ->
      let
        stream = parsecStream query
        mode = parsecResult query
        offset = parsecOffset query
        replyOk tok str = query
          { parsecStream = str
          , parsecOffset = offset + 1
          , parsecResult = Right tok
          }
        replyErr = query
          { parsecResult = Left (ParsecError test []) }
      in
        callback $ case mode of
          -- print mode
          Right tok
            | tokenClass test tok -> replyOk tok (snoc stream tok)
            | otherwise -> replyErr
          -- parse mode
          Left _ -> case uncons stream of
            Just (tok, rest)
              | tokenClass test tok -> replyOk tok rest
              | otherwise -> replyErr
            Nothing -> replyErr
instance BackusNaurForm (Parsector s a b) where
  rule name p = Parsector $ \callback query ->
    flip (runParsector p) query $ \reply -> callback $
      case parsecResult reply of
        Left (ParsecError expect labels) ->
          reply { parsecResult = Left (ParsecError expect [Node name labels]) }
        Right _ -> reply
instance
  ( Categorized token, Item s ~ token
  , Cons s s token token, Snoc s s token token
  ) => TerminalSymbol token (Parsector s () ())
instance Functor (Parsector s a) where
  fmap = rmap
instance Categorized (Item s) => Applicative (Parsector s a) where
  pure b = Parsector $ \callback query ->
    callback query { parsecResult = Right b }
  (<*>) = ap
instance Categorized (Item s) => Monad (Parsector s a) where
  return = pure
  p >>= f = Parsector $ \callback query ->
    flip (runParsector p) query $ \reply ->
      case parsecResult reply of
        Left err -> callback reply {parsecResult = Left err}
        Right b -> runParsector (f b) callback reply
          {parsecResult = parsecResult query}
instance Categorized (Item s) => Alternative (Parsector s a) where
  -- | Always fail, consuming no input and expecting nothing.
  empty = Parsector $ \callback query ->
    callback query { parsecResult = Left mempty }
  p <|> q = mplus (try p) q
instance Categorized (Item s) => MonadPlus (Parsector s a) where
  mplus p q = Parsector $ \callback query ->
    flip (runParsector p) query $ \replyP -> callback $
      case parsecResult replyP of
        Right _ -> replyP
        Left errP -> flip (runParsector q) query $ \replyQ ->
          case parsecResult replyQ of
            Right _ -> replyQ
            Left errQ ->
              case (compare `on` parsecOffset) replyP replyQ of
                LT -> replyQ
                EQ -> replyP {parsecResult = Left (errP <> errQ)}
                GT -> replyP
instance Categorized (Item s) => MonadFail (Parsector s a) where
  fail msg = rule msg empty
instance Categorized (Item s) => MonadTry (Parsector s a) where
  try p = Parsector $ \callback query ->
    flip (runParsector p) query $ \reply -> callback $
      if parsecOffset reply > parsecOffset query
      then case parsecResult reply of
        Left err -> query { parsecResult = Left err }
        Right _  -> reply
      else reply
instance Categorized (Item s) => Filterable (Parsector s a) where
  mapMaybe = dimapMaybe Just
instance Category (Parsector s) where
  id = Parsector id
  Parsector q . Parsector p = Parsector (p . q)
instance Categorized (Item s) => Arrow (Parsector s) where
  arr f = Parsector $ \callback reply -> callback (f <$> reply)
  (***) = (>*<)
  first = first'
  second = second'
instance Categorized (Item s) => ArrowZero (Parsector s) where
  zeroArrow = empty
instance Categorized (Item s) => ArrowPlus (Parsector s) where
  (<+>) = (<|>)
instance Categorized (Item s) => ArrowChoice (Parsector s) where
  (+++) = (>+<)
  left = left'
  right = right'
instance Profunctor (Parsector s) where
  dimap f g (Parsector p) = Parsector $
    dimap (lmap (fmap g)) (lmap (fmap f)) p
instance Strong (Parsector s) where
  first' p = Parsector $ \callback reply0 ->
    flip (runParsector p) (fst <$> reply0) $ \reply1 ->
      callback reply1
        { parsecResult = (,)
            <$> parsecResult reply1
            <*> (snd <$> parsecResult reply0)
        }
  second' p = Parsector $ \callback reply0 ->
    flip (runParsector p) (snd <$> reply0) $ \reply1 ->
      callback reply1
        { parsecResult = (,)
            <$> (fst <$> parsecResult reply0)
            <*> parsecResult reply1
        }
instance Categorized (Item s) => Choice (Parsector s) where
  left' = alternate . Left
  right' = alternate . Right
instance Categorized (Item s) => Distributor (Parsector s) where
  manyP p = Parsector $ \callback query ->
    case parsecResult query of
      Left _ ->
        let
          queryP = query { parsecResult = Left mempty }
        in
          flip (runParsector (try p)) queryP $ \replyP ->
            case parsecResult replyP of
              Left _ ->
                callback query { parsecResult = Right [] }
              Right a ->
                let
                  queryM = replyP { parsecResult = Left mempty }
                in
                  flip (runParsector (manyP p)) queryM $
                    \replyM -> callback replyM
                      {parsecResult = (a:) <$> parsecResult replyM}
      Right _ ->
        runParsector (eotList >~ p >*< manyP p >+< oneP) callback query
instance Categorized (Item s) => Alternator (Parsector s) where
  alternate (Left p) = Parsector $ \callback query -> callback $
    let
      replyOk = query
        { parsecResult = case parsecResult query of
            Left err       -> Left err
            Right (Left a) -> Right a
            Right (Right _) -> Left mempty
        }
      replyErr = query { parsecResult = Left mempty }
    in
      case (parsecResult query, parsecResult replyOk) of
        (Right _, Left _) -> replyErr
        _________________ ->
          flip (runParsector p) replyOk $ \reply -> reply
            { parsecResult = fmap Left (parsecResult reply) }
  alternate (Right p) = Parsector $ \callback query -> callback $
    let
      replyOk = query
        { parsecResult = case parsecResult query of
            Left err        -> Left err
            Right (Left _)  -> Left mempty
            Right (Right b) -> Right b
        }
      replyErr = query { parsecResult = Left mempty }
    in
      case (parsecResult query, parsecResult replyOk) of
        (Right _, Left _) -> replyErr
        _________________ ->
          flip (runParsector p) replyOk $ \reply -> reply
            { parsecResult = fmap Right (parsecResult reply) }
  optionP def p = Parsector $ \callback query ->
    case parsecResult query of
      Left _ -> runParsector (p <|> pureP def) callback query
      Right _ -> runParsector (pureP def <|> p) callback query
instance Categorized (Item s) => Cochoice (Parsector s) where
  unleft = fst . filtrate
  unright = snd . filtrate
instance Categorized (Item s) => Filtrator (Parsector s) where
  filtrate p =
    ( Parsector $ \callback query ->
        flip (runParsector p) (Left <$> query) $ \reply ->
          callback reply
            { parsecResult =
                parsecResult reply >>= either Right (const (Left mempty))
            }
    , Parsector $ \callback query ->
        flip (runParsector p) (Right <$> query) $ \reply ->
          callback reply
            { parsecResult =
                parsecResult reply >>= either (const (Left mempty)) Right
            }
    )
