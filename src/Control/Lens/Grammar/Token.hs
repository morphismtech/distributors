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

  {- | A single token which is `oneOf` a set. -}
  oneOf :: Foldable f => f token -> p
  default oneOf
    :: (p ~ q token token, Choice q, Cochoice q, Foldable f)
    => f token -> p
  oneOf = satisfy . oneOf

  {- | A single token which is `notOneOf` a set. -}
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

instance Categorized token => Tokenized token (token -> Bool) where
  anyToken _ = True
  token = (==)
  oneOf = flip elem
  notOneOf = flip notElem
  asIn = lmap categorize . (==)
  notAsIn = lmap categorize . (/=)

{- | A single token that satisfies a predicate. -}
satisfy
  :: (Tokenized a (p a a), Choice p, Cochoice p)
  => (a -> Bool) -> p a a
satisfy f = satisfied f >?< anyToken

{- | A specified stream of `tokens`.
It can be used as a default definition for the `Data.String.fromString`
method of `Data.String.IsString` when `Tokenized` `Char` `Char`.
-}
tokens
  :: ( Foldable f, Tokenized a (p a a)
     , Monoidal p, Choice p
     , AsEmpty s, Cons s s a a
     )
  => f a -> p s s
tokens = foldr ((>:<) . token) asEmpty

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
