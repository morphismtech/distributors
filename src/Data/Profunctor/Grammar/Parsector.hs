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
  , StateCallbacks (..)
  , Expect (..)
  , parsecP
  , unparsecP
  ) where

import Control.Applicative
import Data.Function
import Control.Lens
import Control.Lens.Grammar.BackusNaur
import Control.Lens.PartialIso
import Control.Lens.Grammar.Symbol
import Control.Lens.Grammar.Token
import Control.Monad
import Control.Monad.Try
import Control.Lens.Grammar.Kleene
import Data.Profunctor
import Data.Profunctor.Distributor
import Data.Profunctor.Filtrator
import GHC.Exts
import Witherable

newtype Parsector s a b = Parsector
  { runParsector :: forall x. StateCallbacks s a b x -> x }

data StateCallbacks s a b x = StateCallbacks
  { stateStream :: s
  , stateOffset :: Word
  , stateSyntax :: Maybe a
  , consumedOk :: b -> s -> Expect s -> x
  , consumedErr :: Expect s -> x
  , emptyOk :: b -> s -> Expect s -> x
  , emptyErr :: Expect s -> x
  }

data Expect s = Expect
  { expectOffset :: Word
  , expectPattern :: Bnf (RegEx (Item s)) -- ^ first set grammar
  }
deriving instance
  ( Categorized (Item s)
  , Show (Item s)
  , Show (Categorize (Item s))
  ) => Show (Expect s)
deriving instance Categorized (Item s) => Eq (Expect s)
deriving instance Categorized (Item s) => Ord (Expect s)

-- | Run a `Parsector` as a parser, consuming tokens from the input.
parsecP :: Parsector s a b -> s -> Either (Expect s, s) (b, s)
parsecP (Parsector p) s = p StateCallbacks
  { stateStream = s
  , stateOffset = 0
  , stateSyntax = Nothing
  , consumedOk = \b st _ -> Right (b, st)
  , consumedErr = \err -> Left (err, s)
  , emptyOk = \b st _ -> Right (b, st)
  , emptyErr = \err -> Left (err, s)
  }

-- | Run a `Parsector` as an unparser, snocing tokens onto an empty input.
unparsecP :: Parsector s a b -> a -> s -> Either (Expect s, s) s
unparsecP (Parsector p) a s = snd <$> p StateCallbacks
  { stateStream = s
  , stateOffset = 0
  , stateSyntax = Just a
  , consumedOk = \b st _ -> Right (b, st)
  , consumedErr = \err -> Left (err, s)
  , emptyOk = \b st _ -> Right (b, st)
  , emptyErr = \err -> Left (err, s)
  }

-- Parsector instances
instance Categorized (Item s) => Semigroup (Expect s) where
  e1 <> e2 = case compare (expectOffset e1) (expectOffset e2) of
    GT -> e1
    LT -> e2
    EQ -> Expect
      { expectOffset = expectOffset e1
      , expectPattern = expectPattern e1 >|< expectPattern e2
      }
instance Categorized (Item s) => Monoid (Expect s) where
  mempty = Expect
    { expectOffset = 0
    , expectPattern = zeroK
    }
instance Profunctor (Parsector s) where
  dimap f g p = Parsector $ \args -> runParsector p args
    { stateSyntax = fmap f (stateSyntax args)
    , consumedOk = consumedOk args . g
    , emptyOk = emptyOk args . g
    }
instance Functor (Parsector s a) where
  fmap = rmap
instance Categorized (Item s) => Applicative (Parsector s a) where
  pure b = Parsector $ \args ->
    emptyOk args b (stateStream args) Expect
      { expectOffset = stateOffset args
      , expectPattern = zeroK
      }
  (<*>) = ap
instance Categorized (Item s) => Alternative (Parsector s a) where
  empty = Parsector $ \args -> emptyErr args Expect
    { expectOffset = stateOffset args
    , expectPattern = zeroK
    }
  p <|> q = try p `mplus` q
instance Categorized (Item s) => Monad (Parsector s a) where
  p >>= k = Parsector $ \args -> runParsector p args
    { consumedOk = \b st' err -> runParsector (k b) args
        { stateStream = st'
        , stateOffset = expectOffset err
        , emptyOk = \x st'' err' -> consumedOk args x st'' (err <> err')
        , emptyErr = \err' -> consumedErr args (err <> err')
        }
    , emptyOk = \b st' err -> runParsector (k b) args
        { stateStream = st'
        , stateOffset = expectOffset err
        , emptyOk = \x st'' err' -> emptyOk args x st'' (err <> err')
        , emptyErr = \err' -> emptyErr args (err <> err')
        }
    }
instance Categorized (Item s) => MonadPlus (Parsector s a) where
  p `mplus` q = Parsector $ \args -> runParsector p args
    { emptyErr = \err -> runParsector q args
        { emptyOk = \syn str err' -> emptyOk args syn str (err <> err')
        , emptyErr = \err' -> emptyErr args (err <> err')
        }
    }
instance Categorized (Item s) => MonadFail (Parsector s a) where
  fail msg = rule msg empty
instance Categorized (Item s) => MonadTry (Parsector s a) where
  try (Parsector p) = Parsector $ \args ->
    p args { consumedErr = emptyErr args }
instance Categorized (Item s) => Filterable (Parsector s a) where
  mapMaybe = dimapMaybe Just
instance Categorized (Item s) => Alternator (Parsector s) where
  alternate (Left p) = Parsector $ \args ->
    case stateSyntax args of
      Just (Right _) -> emptyErr args Expect
        { expectOffset = stateOffset args
        , expectPattern = zeroK
        }
      mEAC -> runParsector p args
        { stateSyntax = mEAC >>= either Just (const Nothing)
        , consumedOk = \b st' err -> consumedOk args (Left b) st' err
        , emptyOk = \b st' err -> emptyOk args (Left b) st' err
        }
  alternate (Right p) = Parsector $ \args ->
    case stateSyntax args of
      Just (Left _) -> emptyErr args Expect
        { expectOffset = stateOffset args
        , expectPattern = zeroK
        }
      mEAC -> runParsector p args
        { stateSyntax = mEAC >>= either (const Nothing) Just
        , consumedOk = \d st' err -> consumedOk args (Right d) st' err
        , emptyOk = \d st' err -> emptyOk args (Right d) st' err
        }
instance Categorized (Item s) => Choice (Parsector s) where
  left' = alternate . Left
  right' = alternate . Right
instance Categorized (Item s) => Distributor (Parsector s) where
  x >+< y = alternate (Right y) <|> alternate (Left x)
instance Categorized (Item s) => Filtrator (Parsector s) where
  filtrate (Parsector p) =
    ( Parsector $ \args ->
        p args
          { stateSyntax = Left <$> stateSyntax args
          , consumedOk = \ebd st' err -> case ebd of
              Left b -> consumedOk args b st' err
              Right _ -> consumedErr args err
          , emptyOk = \ebd st' err -> case ebd of
              Left b -> emptyOk args b st' err
              Right _ -> emptyErr args err
          }
    , Parsector $ \args ->
        p args
          { stateSyntax = Right <$> stateSyntax args
          , consumedOk = \ebd st' err -> case ebd of
              Right d -> consumedOk args d st' err
              Left _ -> consumedErr args err
          , emptyOk = \ebd st' err -> case ebd of
              Right d -> emptyOk args d st' err
              Left _ -> emptyErr args err
          }
    )
instance Categorized (Item s) => Cochoice (Parsector s) where
  unleft = fst . filtrate
  unright = snd . filtrate
instance
  ( Categorized token, Item s ~ token
  , Cons s s token token, Snoc s s token token
  ) => TokenAlgebra token (Parsector s token token) where
    tokenClass test = Parsector $ \args ->
      let
        str = stateStream args
        off = stateOffset args
        failExp = Expect off (tokenClass test)
        succExp = Expect (off + 1) zeroK
      in
        case stateSyntax args of
          Just tok
            | tokenClass test tok ->
                consumedOk args tok (snoc str tok) succExp
            | otherwise -> emptyErr args failExp
          Nothing -> case uncons str of
            Nothing -> emptyErr args failExp
            Just (tok, rest)
              | tokenClass test tok ->
                  consumedOk args tok rest succExp
              | otherwise -> emptyErr args failExp
instance
  ( Categorized token, Item s ~ token
  , Cons s s token token, Snoc s s token token
  ) => TerminalSymbol token (Parsector s () ())
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
instance Categorized (Item s)
  => BackusNaurForm (Parsector s a b) where
  rule name (Parsector p) = Parsector $ \args -> p args
    { emptyOk = \b st' -> emptyOk args b st' . label
    , emptyErr = emptyErr args . label
    }
    where
      label fl = fl
        { expectPattern = rule name (expectPattern fl)}
  ruleRec name f = rule name (fix f)
