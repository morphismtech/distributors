{-|
Module      : Data.Profunctor.Grammar.Parsector
Description : Parsec-style invertible parser profunctor
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Data.Profunctor.Grammar.Parsector2
  ( -- * Parsector
    Parsector (..)
  , Reply (..)
  , parsecP
  , unparsecP
  ) where

import Control.Applicative
import Control.Category
import Data.Function hiding (id, (.))
import Control.Lens
import Control.Lens.Grammar.BackusNaur
-- import Control.Lens.PartialIso
-- import Control.Lens.Grammar.Symbol
import Control.Lens.Grammar.Token
import Control.Monad
import Control.Lens.Grammar.Kleene
-- import Data.Profunctor
-- import Data.Profunctor.Distributor
-- import Data.Profunctor.Filtrator
import Data.Profunctor.Monadic (MonadTry (..))
import GHC.Exts
import Prelude hiding (id, (.))
-- import Witherable

newtype Parsector s a b = Parsector
  { runParsector :: forall x. (Reply s b -> x) -> Reply s a -> x }

data Reply s a = Reply
  { parsecOffset :: Word
  , parsecExpect :: Bnf (RegEx (Item s))
  , parsecStream :: s -- ^ input stream
  , parsecResult :: Maybe a
  } deriving Functor

parsecP
  :: Categorized (Item s)
  => Parsector s a b -> s -> Reply s b
parsecP (Parsector p) s = p id (Reply 0 zeroK s Nothing)

unparsecP
  :: Categorized (Item s)
  => Parsector s a b -> a -> s -> Reply s b
unparsecP (Parsector p) a s = p id (Reply 0 zeroK s (Just a))

-- Parsector instances
instance Profunctor (Parsector s) where
  dimap f g (Parsector p) = Parsector $
    dimap (lmap (fmap g)) (lmap (fmap f)) p
instance Functor (Parsector s a) where
  fmap = rmap
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
    tokenClass test = Parsector $ \callbacks reply ->
      let
        stream = parsecStream reply
        result = parsecResult reply
        offset = parsecOffset reply
        callbackOk tok str = callbacks Reply
          { parsecStream = str
          , parsecOffset = offset + 1
          , parsecExpect = zeroK
          , parsecResult = Just tok
          }
        callbackErr = callbacks reply
          { parsecExpect = tokenClass test
          , parsecResult = Nothing
          }
      in
        case result of
          Just tok
            | tokenClass test tok -> callbackOk tok (snoc stream tok)
            | otherwise -> callbackErr
          Nothing -> case uncons stream of
            Just (tok, rest)
              | tokenClass test tok -> callbackOk tok rest
              | otherwise -> callbackErr
            Nothing -> callbackErr
instance Categorized (Item s)
  => BackusNaurForm (Parsector s a b) where
  rule name p = Parsector $ \callbacks reply0 ->
    flip (runParsector p) reply0 $ \reply1 ->
      case parsecResult reply1 of
        Nothing -> callbacks reply1
          {parsecExpect = rule name (parsecExpect reply1)}
        Just _ -> callbacks reply1
  ruleRec name f = rule name (fix f)
instance Categorized (Item s) => Applicative (Parsector s a) where
  pure b = Parsector $ \callbacks reply ->
    callbacks reply
      { parsecExpect = zeroK
      , parsecResult = Just b
      }
  (<*>) = ap
instance Categorized (Item s) => Monad (Parsector s a) where
  return = pure
  p >>= f = Parsector $ \callbacks reply ->
    flip (runParsector p) reply $ \reply0 ->
      case parsecResult reply0 of
        Nothing -> callbacks reply0 {parsecResult = Nothing}
        Just b -> runParsector (f b) callbacks reply0
          {parsecResult = parsecResult reply}
instance Categorized (Item s) => Alternative (Parsector s a) where
  empty = Parsector $ \callbacks reply ->
    callbacks reply
      { parsecExpect = zeroK
      , parsecResult = Nothing
      }
  p <|> q = Parsector $ \callbacks reply ->
    flip (runParsector p) reply $ \reply0 ->
    flip (runParsector q) reply $ \reply1 ->
      case (parsecResult reply0, parsecResult reply1) of
        (Just _, Nothing) -> callbacks reply0
        (Nothing, Just _) -> callbacks reply1
        -- longest passing match
        (Just _, Just _) ->
          if ((>=) `on` parsecOffset) reply0 reply1
          then callbacks reply0
          else callbacks reply1
        -- longest failing match
        (Nothing, Nothing) ->
          case (compare `on` parsecOffset) reply0 reply1 of
            GT -> callbacks reply0
            EQ -> callbacks reply0
              {parsecExpect = ((>|<) `on` parsecExpect) reply0 reply1}
            LT -> callbacks reply1
instance Categorized (Item s) => MonadPlus (Parsector s a)
instance Categorized (Item s) => MonadFail (Parsector s a) where
  fail msg = rule msg empty
instance Categorized (Item s) => MonadTry (Parsector s a) where
  try = undefined -- TODO isempty === offset == 0
instance Category (Parsector s) where
  id = Parsector ($)
  Parsector q . Parsector p = Parsector (p . q)
-- instance Categorized (Item s) => Filterable (Parsector s a) where
--   mapMaybe = dimapMaybe Just
-- instance Categorized (Item s) => Alternator (Parsector s) where
--   alternate (Left p) = Parsector $ \args ->
--     case stateSyntax args of
--       Just (Right _) -> emptyErr args Expect
--         { expectOffset = stateOffset args
--         , expectPattern = zeroK
--         }
--       mEAC -> runParsector p args
--         { stateSyntax = mEAC >>= either Just (const Nothing)
--         , callbackOk = \b st' err -> callbackOk args (Left b) st' err
--         , emptyOk = \b st' err -> emptyOk args (Left b) st' err
--         }
--   alternate (Right p) = Parsector $ \args ->
--     case stateSyntax args of
--       Just (Left _) -> emptyErr args Expect
--         { expectOffset = stateOffset args
--         , expectPattern = zeroK
--         }
--       mEAC -> runParsector p args
--         { stateSyntax = mEAC >>= either (const Nothing) Just
--         , callbackOk = \d st' err -> callbackOk args (Right d) st' err
--         , emptyOk = \d st' err -> emptyOk args (Right d) st' err
--         }
-- instance Categorized (Item s) => Choice (Parsector s) where
--   left' = alternate . Left
--   right' = alternate . Right
-- instance Categorized (Item s) => Distributor (Parsector s)
-- instance Categorized (Item s) => Filtrator (Parsector s) where
--   filtrate (Parsector p) =
--     ( Parsector $ \args ->
--         p args
--           { stateSyntax = Left <$> stateSyntax args
--           , callbackOk = \ebd st' err -> case ebd of
--               Left b -> callbackOk args b st' err
--               Right _ -> callbackErr args err
--           , emptyOk = \ebd st' err -> case ebd of
--               Left b -> emptyOk args b st' err
--               Right _ -> emptyErr args err
--           }
--     , Parsector $ \args ->
--         p args
--           { stateSyntax = Right <$> stateSyntax args
--           , callbackOk = \ebd st' err -> case ebd of
--               Right d -> callbackOk args d st' err
--               Left _ -> callbackErr args err
--           , emptyOk = \ebd st' err -> case ebd of
--               Right d -> emptyOk args d st' err
--               Left _ -> emptyErr args err
--           }
--     )
-- instance Categorized (Item s) => Cochoice (Parsector s) where
--   unleft = fst . filtrate
--   unright = snd . filtrate
-- instance
--   ( Categorized token, Item s ~ token
--   , Cons s s token token, Snoc s s token token
--   ) => TokenAlgebra token (Parsector s token token) where
--     tokenClass test = Parsector $ \args ->
--       let
--         str = stateStream args
--         off = stateOffset args
--         failExp = Expect off (tokenClass test)
--         succExp = Expect off zeroK
--       in
--         case stateSyntax args of
--           Just tok
--             | tokenClass test tok ->
--                 callbackOk args tok (snoc str tok) succExp
--             | otherwise -> emptyErr args failExp
--           Nothing -> case uncons str of
--             Nothing -> emptyErr args failExp
--             Just (tok, rest)
--               | tokenClass test tok ->
--                   callbackOk args tok rest succExp
--               | otherwise -> emptyErr args failExp
-- instance
--   ( Categorized token, Item s ~ token
--   , Cons s s token token, Snoc s s token token
--   ) => TerminalSymbol token (Parsector s () ())
-- instance
--   ( Categorized token, Item s ~ token
--   , Cons s s token token, Snoc s s token token
--   ) => Tokenized token (Parsector s token token) where
--   anyToken = tokenClass anyToken
--   token t = tokenClass (token t)
--   oneOf ts = tokenClass (oneOf ts)
--   notOneOf ts = tokenClass (notOneOf ts)
--   asIn cat = tokenClass (asIn cat)
--   notAsIn cat = tokenClass (notAsIn cat)
-- instance Categorized (Item s)
--   => BackusNaurForm (Parsector s a b) where
--   rule name (Parsector p) = Parsector $ \args -> p args
--     { emptyOk = \b st' -> emptyOk args b st' . label
--     , emptyErr = emptyErr args . label
--     }
--     where
--       label fl = fl
--         { expectPattern = rule name (expectPattern fl)}
--   ruleRec name f = rule name (fix f)
