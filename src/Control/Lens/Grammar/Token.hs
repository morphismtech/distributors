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
  , fromTokens
  , terminator
    -- * Like
  , oneLike
  , manyLike
  , optLike
  , someLike
    -- * Categorized
  , Categorized (..)
  , GeneralCategory (..)
  ) where

import Control.Lens
import Control.Lens.PartialIso
import Data.Char
import Data.Profunctor
import Data.Profunctor.Distributor
import Data.Profunctor.Monoidal
import Data.Word

class (Ord token, Ord (Categorize token)) => Categorized token where
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

class Categorized token => Tokenized token p | p -> token where
  anyToken :: p

  token :: token -> p
  default token
    :: (p ~ q token token, Choice q, Cochoice q)
    => token -> p
  token = satisfy . token

  oneOf :: Foldable f => f token -> p
  default oneOf
    :: (p ~ q token token, Choice q, Cochoice q, Foldable f)
    => f token -> p
  oneOf = satisfy . oneOf

  notOneOf :: Foldable f => f token -> p
  default notOneOf
    :: (p ~ q token token, Choice q, Cochoice q, Foldable f)
    => f token -> p
  notOneOf = satisfy . notOneOf

  asIn :: Categorize token -> p
  default asIn
    :: (p ~ q token token, Choice q, Cochoice q)
    => Categorize token -> p
  asIn = satisfy . asIn

  notAsIn :: Categorize token -> p
  default notAsIn
    :: (p ~ q token token, Choice q, Cochoice q)
    => Categorize token -> p
  notAsIn = satisfy . notAsIn

instance Categorized token => Tokenized token (token -> Bool) where
  anyToken _ = True
  token = (==)
  oneOf = flip elem
  notOneOf = flip notElem
  asIn = lmap categorize . (==)
  notAsIn = lmap categorize . (/=)

satisfy
  :: (Tokenized a (p a a), Choice p, Cochoice p)
  => (a -> Bool) -> p a a
satisfy f = satisfied f >?< anyToken

fromTokens
  :: ( Foldable f, Tokenized a (p a a)
     , Monoidal p, Choice p
     , AsEmpty s, Cons s s a a
     )
  => f a -> p s s
fromTokens = foldr ((>:<) . token) asEmpty

terminator
  :: ( Foldable f, Tokenized a (p a a)
     , Monoidal p, Cochoice p
     )
  => f a -> p () ()
terminator = foldr (\a p -> only a ?< anyToken *> p) oneP

{- |
`oneLike` consumes one token
of a given token's category while parsing,
and produces the given token while printing.
-}
oneLike
  :: forall token p. (Profunctor p, Tokenized token (p token token))
  => token -> p () ()
oneLike a = dimap preF postF catA
  where
    preF _ = a
    postF (_:: token) = ()
    catA = asIn (categorize a)

{- |
`manyLike` consumes zero or more tokens
of a given token's category while parsing,
and produces no tokens printing.
-}
manyLike
  :: forall token p. (Distributor p, Tokenized token (p token token))
  => token -> p () ()
manyLike a = dimap preF postF (manyP catA)
  where
    preF _ = []::[token]
    postF (_::[token]) = ()
    catA = asIn (categorize a)

{- |
`optLike` consumes zero or more tokens
of a given token's category while parsing,
and produces the given token while printing.
-}
optLike
  :: forall token p. (Distributor p, Tokenized token (p token token))
  => token -> p () ()
optLike a = dimap preF postF (manyP catA)
  where
    preF _ = [a]::[token]
    postF (_::[token]) = ()
    catA = asIn (categorize a)

{- |
`someLike` consumes one or more tokens
of a given token's category while parsing,
and produces the given token while printing.
-}
someLike
  :: forall token p. (Distributor p, Tokenized token (p token token))
  => token -> p () ()
someLike a = dimap preF postF (catA >*< manyP catA)
  where
    preF _ = (a, []::[token])
    postF (_::token, _::[token]) = ()
    catA = asIn (categorize a)
