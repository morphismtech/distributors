{-|
Module      : Data.Profunctor.Grammar.Parsector
Description : Parsec-style invertible parser profunctor
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
import Control.Lens.PartialIso
import Control.Lens.Grammar.Symbol
import Control.Lens.Grammar.Token
import Control.Monad
import Control.Lens.Grammar.Kleene
import Data.Profunctor
import Data.Profunctor.Distributor
import Data.Profunctor.Filtrator
import Data.Profunctor.Monadic (MonadTry (..))
import Data.Profunctor.Monoidal
import GHC.Exts
import Prelude hiding (id, (.))
import Witherable

newtype Parsector s a b = Parsector
  { runParsector :: forall x. (Reply s b -> x) -> Reply s a -> x }

data Reply s a = Reply
  { parsecOffset :: Word
  , parsecResult :: Either (Bnf (RegEx (Item s))) a
  , parsecStream :: s -- ^ input stream
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

parsecP :: Categorized (Item s) => Parsector s a b -> s -> Reply s b
parsecP p s = runParsector p id (Reply 0 (Left zeroK) s)

unparsecP :: Parsector s a b -> a -> s -> Reply s b
unparsecP p a s = runParsector p id (Reply 0 (Right a) s)

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
        replyOk tok str = Reply
          { parsecStream = str
          , parsecOffset = offset + 1
          , parsecResult = Right tok
          }
        replyErr = query
          { parsecResult = Left (tokenClass test) }
      in
        callback $ case result of
          Right tok
            | tokenClass test tok -> replyOk tok (snoc stream tok)
            | otherwise -> replyErr
          Left _ -> case uncons stream of
            Just (tok, rest)
              | tokenClass test tok -> replyOk tok rest
              | otherwise -> replyErr
            Nothing -> replyErr
instance Categorized (Item s)
  => BackusNaurForm (Parsector s a b) where
  rule name p = Parsector $ \callback query ->
    flip (runParsector p) query $ \reply -> callback $
      case parsecResult reply of
        Left expect -> reply
          {parsecResult = Left (rule name expect)}
        Right _ -> reply
  ruleRec name f = rule name (fix f)
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
        Left expect -> callback reply {parsecResult = Left expect}
        Right b -> runParsector (f b) callback reply
          {parsecResult = parsecResult query}
instance Categorized (Item s) => Alternative (Parsector s a) where
  -- | Always fail, consuming no input and expecting nothing.
  empty = Parsector $ \callback query ->
    callback query { parsecResult = Left zeroK }
  p <|> q = Parsector $ \callback query ->
    -- Run p on the original input.
    flip (runParsector p) query $ \replyP -> callback $
      case (parsecResult query, parsecResult replyP) of
        -- In unparse mode the query already carries a value (Right _).
        -- If p succeeded, commit immediately without running q.
        (Right _, Right _) -> replyP
        -- In parse mode (or when p failed), run q on the same input.
        __________________ ->
          flip (runParsector q) query $ \replyQ ->
            case (parsecResult replyP, parsecResult replyQ) of
              -- Only one branch succeeded: take it.
              (Right _, Left _) -> replyP
              (Left _, Right _) -> replyQ
              -- Both succeeded: take the longest match.
              (Right _, Right _) ->
                if parsecOffset replyP >= parsecOffset replyQ
                then replyP
                else replyQ
              -- Both failed: report the furthest failure,
              -- merging expected tokens on a tie.
              (Left expectP, Left expectQ) ->
                case compare (parsecOffset replyP) (parsecOffset replyQ) of
                  GT -> replyP
                  EQ -> replyP { parsecResult = Left (expectP >|< expectQ) }
                  LT -> replyQ
instance Categorized (Item s) => MonadPlus (Parsector s a)
instance Categorized (Item s) => MonadFail (Parsector s a) where
  fail msg = rule msg empty
instance Categorized (Item s) => MonadTry (Parsector s a) where
  try p = Parsector $ \callback query ->
    flip (runParsector p) query $ \reply -> callback $
      case parsecResult reply of
        Right _ -> reply
        Left _ -> query { parsecResult = Left zeroK }
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
instance Categorized (Item s) => Distributor (Parsector s)
instance Categorized (Item s) => Alternator (Parsector s) where
  alternate (Left p) = Parsector $ \callback query -> callback $
    let
      replyOk = query
        { parsecResult = do
            result <- parsecResult query
            either Right (const (Left zeroK)) result
        }
      replyErr = query
        { parsecResult = Left zeroK }
    in
      case (parsecResult query, parsecResult replyOk) of
        (Right _, Left _) -> replyErr
        _________________ ->
          flip (runParsector p) replyOk $ \reply -> reply
            { parsecResult = Left <$> parsecResult reply }
  alternate (Right p) = Parsector $ \callback query -> callback $
    let
      replyOk = query
        { parsecResult = do
            result <- parsecResult query
            either (const (Left zeroK)) Right result
        }
      replyErr = query
        { parsecResult = Left zeroK }
    in
      case (parsecResult query, parsecResult replyOk) of
        (Right _, Left _) -> replyErr
        _________________ ->
          flip (runParsector p) replyOk $ \reply -> reply
            { parsecResult = Right <$> parsecResult reply }
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
                either Right (const (Left zeroK)) result
            }
    , Parsector $ \callback query ->
        flip (runParsector p) (Right <$> query) $ \reply ->
          callback reply
            { parsecResult = do
                result <- parsecResult reply
                either (const (Left zeroK)) Right result
            }
    )
