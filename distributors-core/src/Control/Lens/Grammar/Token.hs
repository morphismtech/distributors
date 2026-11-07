{- |
Module      : Control.Lens.Grammar.Token
Description : lexical tokens
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Control.Lens.Grammar.Token
  ( -- * Tokenized
    Tokenized (..)
  , satisfy
  , tokens
    -- * Categorized
  , Categorized (..)
  , GeneralCategory (..)
  ) where

import Control.Lens
import Control.Lens.PartialIso
import Control.Monad.Loops (iterateUntil)
import Data.Bifunctor.Joker
import Data.Char
import Data.Foldable
import Data.Profunctor
import Data.Profunctor.Monoidal
import Data.Word
import Control.Monad.State (StateT, state)
import System.Random (RandomGen, Random, random, randomR)
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen (Gen)
import qualified Test.QuickCheck.Gen as Gen
import Text.ParserCombinators.ReadP (ReadP)
import qualified Text.ParserCombinators.ReadP as ReadP

{- | `Categorized` provides a type family `Categorize`
and a function to `categorize` tokens into disjoint categories.

>>> :kind! Categorize Char
Categorize Char :: *
= GeneralCategory

>>> categorize 'a'
LowercaseLetter
-}
class (Ord token, Ord (Categorize token), Enum (Categorize token))
  => Categorized token where
  type Categorize token
  type Categorize token = ()
  categorize :: token -> Categorize token
  default categorize :: Categorize token ~ () => token -> Categorize token
  categorize _ = ()
instance Categorized Char where
  type Categorize Char = GeneralCategory
  categorize = generalCategory
instance Categorized Word8
instance Categorized ()

{- | `Tokenized` combinators for constructing lexical tokens. -}
class Categorized token => Tokenized token p | p -> token where
  {- | Any single token. -}
  anyToken :: p

  {- | A single specified `token`. -}
  token :: token -> p
  default token
    :: (p ~ q token token, Choice q, Cochoice q)
    => token -> p
  token = satisfy . token

  {- | A single token which is `oneOf` a set.

  prop> token x = oneOf [x]
  
  -}
  oneOf :: Foldable f => f token -> p
  default oneOf
    :: (p ~ q token token, Choice q, Cochoice q, Foldable f)
    => f token -> p
  oneOf = satisfy . oneOf

  {- | A single token which is `notOneOf` a set.
  
  prop> anyToken = notOneOf []
  
  -}
  notOneOf :: Foldable f => f token -> p
  default notOneOf
    :: (p ~ q token token, Choice q, Cochoice q, Foldable f)
    => f token -> p
  notOneOf = satisfy . notOneOf

  {- | A single token which is `asIn` a category. -}
  asIn :: Categorize token -> p
  default asIn
    :: (p ~ q token token, Choice q, Cochoice q)
    => Categorize token -> p
  asIn = satisfy . asIn

  {- | A single token which is `notAsIn` a category. -}
  notAsIn :: Categorize token -> p
  default notAsIn
    :: (p ~ q token token, Choice q, Cochoice q)
    => Categorize token -> p
  notAsIn = satisfy . notAsIn

{- | A single token that satisfies a predicate. -}
satisfy
  :: (Tokenized a (p a a), Choice p, Cochoice p)
  => (a -> Bool) -> p a a
satisfy f = satisfied f >?< anyToken

{- | A specified stream of `tokens`. -}
tokens
  :: ( Foldable f, Tokenized a (p a a)
     , Monoidal p, Choice p
     , AsEmpty s, Cons s s a a
     )
  => f a -> p s s
tokens = foldr ((>:<) . token) asEmpty

-- instances
instance Categorized token => Tokenized token (token -> Bool) where
  anyToken _ = True
  token = (==)
  oneOf = flip elem
  notOneOf = flip notElem
  asIn = lmap categorize . (==)
  notAsIn = lmap categorize . (/=)
instance Tokenized token (f token)
  => Tokenized token (Joker f token token) where
    anyToken = Joker (anyToken @token)
    token = Joker . token @token
    oneOf = Joker . oneOf @token
    notOneOf = Joker . notOneOf @token
    asIn = Joker . asIn @token
    notAsIn = Joker . notAsIn @token
instance Tokenized Char (ReadP Char) where
  anyToken = ReadP.get
  token = ReadP.char
  oneOf = ReadP.satisfy . oneOf
  notOneOf = ReadP.satisfy . notOneOf
  asIn = ReadP.satisfy . asIn
  notAsIn = ReadP.satisfy . notAsIn
instance (Categorized token, Arbitrary token) => Tokenized token (Gen token) where
  anyToken = arbitrary @token
  token = pure
  oneOf = Gen.elements . toList
  notOneOf xs = arbitrary `Gen.suchThat` (`notElem` xs)
  asIn cat = arbitrary `Gen.suchThat` ((==) cat . categorize)
  notAsIn cat = arbitrary `Gen.suchThat` ((/=) cat . categorize)
instance (RandomGen g, Monad m, Categorized token, Random token)
  => Tokenized token (StateT g m token) where
  anyToken = state random
  token = pure
  oneOf xs = do
    let ys = toList xs
    i <- state (randomR (0, length ys - 1))
    pure (ys !! i)
  notOneOf xs = iterateUntil (`notElem` xs) anyToken
  asIn cat = iterateUntil ((== cat) . categorize) anyToken
  notAsIn cat = iterateUntil ((/= cat) . categorize) anyToken
