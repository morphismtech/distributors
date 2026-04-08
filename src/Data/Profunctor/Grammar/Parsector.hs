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
  , Reply (..)
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
import GHC.Exts
import Prelude hiding (id, (.))
import Witherable

{- | `Parsector` is an invertible parser which can be used
to parse with `parsecP` or print with `unparsecP`,
yielding a `Reply`, with detailed errors and offset tracking.

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
  { runParsector :: forall x. (Reply s b -> x) -> Reply s a -> x }

{- | `Reply` is the return type for `parsecP` & `unparsecP`.
It's the fundamental building block of `Parsector`.
-}
data Reply s a = Reply
  { parsecOffset :: !Word
    -- ^ number of tokens either parsed or printed
  , parsecExpect :: TokenClass (Item s)
  , parsecResult :: Maybe a
    {- ^ As an input `parsecResult` represents either parse mode,
    or print mode with an input syntax value.
    As an output `parsecResult` represents either failure
    with the expected `TokenClass`,
    or success with an output syntax value.
    -}
  , parsecStream :: s -- ^ both input and output stream
  } deriving (Functor, Foldable, Traversable)
deriving stock instance
  ( Categorized (Item s)
  , Show (Item s), Show (Categorize (Item s))
  , Show a, Show s
  ) => Show (Reply s a)
deriving stock instance
  ( Categorized (Item s)
  , Read (Item s), Read (Categorize (Item s))
  , Read a, Read s
  ) => Read (Reply s a)
deriving stock instance
  ( Categorized (Item s)
  , Eq a, Eq s
  ) => Eq (Reply s a)
deriving stock instance
  ( Categorized (Item s)
  , Ord a, Ord s
  ) => Ord (Reply s a)

-- | `Parsector` is parsed using `parsecP`.
parsecP :: Categorized (Item s) => Parsector s a b -> s -> Reply s b
parsecP p s = runParsector p id (Reply 0 falseB Nothing s)

-- | `Parsector` is printed using `unparsecP`.
unparsecP :: Categorized (Item s) => Parsector s a b -> a -> s -> Reply s b
unparsecP p a s = runParsector p id (Reply 0 falseB (Just a) s)

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
        result = parsecResult query
        offset = parsecOffset query
        replyOk tok str = query
          { parsecStream = str
          , parsecOffset = offset + 1
          , parsecResult = Just tok
          }
        replyErr = query
          { parsecExpect = test
          , parsecResult = Nothing
          }
      in
        callback $ case result of
          Just tok
            | tokenClass test tok -> replyOk tok (snoc stream tok)
            | otherwise -> replyErr
          Nothing -> case uncons stream of
            Just (tok, rest)
              | tokenClass test tok -> replyOk tok rest
              | otherwise -> replyErr
            Nothing -> replyErr
instance BackusNaurForm (Parsector s a b)
instance
  ( Categorized token, Item s ~ token
  , Cons s s token token, Snoc s s token token
  ) => TerminalSymbol token (Parsector s () ())
instance Functor (Parsector s a) where
  fmap = rmap
instance Categorized (Item s) => Applicative (Parsector s a) where
  pure b = Parsector $ \callback query ->
    callback query { parsecResult = Just b }
  (<*>) = ap
instance Categorized (Item s) => Monad (Parsector s a) where
  return = pure
  p >>= f = Parsector $ \callback query ->
    flip (runParsector p) query $ \reply ->
      case parsecResult reply of
        Nothing -> callback reply {parsecResult = Nothing}
        Just b -> runParsector (f b) callback reply
          {parsecResult = parsecResult query}
instance Categorized (Item s) => Alternative (Parsector s a) where
  -- | Always fail, consuming no input and expecting nothing.
  empty = Parsector $ \callback query ->
    callback query { parsecResult = Nothing }
  p <|> q = mplus (try p) q
instance Categorized (Item s) => MonadPlus (Parsector s a) where
  mplus p q = Parsector $ \callback query ->
    let
      offset0 = parsecOffset query
    in
      flip (runParsector p) query $ \replyP -> callback $
        if parsecOffset replyP == offset0
        then case parsecResult replyP of
          Nothing ->
            flip (runParsector q) query $ \replyQ ->
              if parsecOffset replyQ == offset0
              then replyQ
                {parsecExpect = ((>||<) `on` parsecExpect) replyP replyQ}
              else replyQ
          Just _ -> replyP
        else replyP
instance Categorized (Item s) => MonadFail (Parsector s a) where
  fail msg = rule msg empty
instance Categorized (Item s) => MonadTry (Parsector s a) where
  try p = Parsector $ \callback query ->
    flip (runParsector p) query $ \reply -> callback $
      if parsecOffset reply > 0
      then case parsecResult reply of
        Nothing -> query
          { parsecExpect = parsecExpect reply
          , parsecResult = Nothing
          }
        Just _ -> reply
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
      Nothing ->
        let
          queryP = Reply
            { parsecOffset = parsecOffset query
            , parsecExpect = parsecExpect query
            , parsecResult = Nothing
            , parsecStream = parsecStream query
            }
        in
          flip (runParsector (try p)) queryP $ \replyP ->
            case parsecResult replyP of
              Nothing ->
                callback Reply
                  { parsecOffset = parsecOffset query
                  , parsecExpect = parsecExpect query
                  , parsecResult = Just []
                  , parsecStream = parsecStream query
                  }
              Just a ->
                let
                  queryM = Reply
                    { parsecOffset = parsecOffset replyP
                    , parsecExpect = parsecExpect replyP
                    , parsecResult = Nothing
                    , parsecStream = parsecStream replyP
                    }
                in
                  flip (runParsector (manyP p)) queryM $
                    \replyM -> callback replyM
                      {parsecResult = (a:) <$> parsecResult replyM}
      Just _ ->
        runParsector (eotList >~ p >*< manyP p >+< oneP) callback query
instance Categorized (Item s) => Alternator (Parsector s) where
  alternate (Left p) = Parsector $ \callback query -> callback $
    let
      replyOk = query
        { parsecResult = do
            result <- parsecResult query
            either Just (const Nothing) result
        }
      replyErr = query
        { parsecResult = Nothing }
    in
      case (parsecResult query, parsecResult replyOk) of
        (Just _, Nothing) -> replyErr
        _________________ ->
          flip (runParsector p) replyOk $ \reply -> reply
            { parsecResult = Left <$> parsecResult reply }
  alternate (Right p) = Parsector $ \callback query -> callback $
    let
      replyOk = query
        { parsecResult = do
            result <- parsecResult query
            either (const Nothing) Just result
        }
      replyErr = query
        { parsecResult = Nothing }
    in
      case (parsecResult query, parsecResult replyOk) of
        (Just _, Nothing) -> replyErr
        _________________ ->
          flip (runParsector p) replyOk $ \reply -> reply
            { parsecResult = Right <$> parsecResult reply }
  optionP def p = Parsector $ \callback query ->
    case parsecResult query of
      Nothing -> runParsector (p <|> pureP def) callback query
      Just _ -> runParsector (pureP def <|> p) callback query
instance Categorized (Item s) => Cochoice (Parsector s) where
  unleft = fst . filtrate
  unright = snd . filtrate
instance Categorized (Item s) => Filtrator (Parsector s) where
  filtrate p =
    ( Parsector $ \callback query ->
        flip (runParsector p) (Left <$> query) $ \reply ->
          callback reply
            { parsecResult = do
                result <- parsecResult reply
                either Just (const Nothing) result
            }
    , Parsector $ \callback query ->
        flip (runParsector p) (Right <$> query) $ \reply ->
          callback reply
            { parsecResult = do
                result <- parsecResult reply
                either (const Nothing) Just result
            }
    )
