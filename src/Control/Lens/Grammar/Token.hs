module Control.Lens.Grammar.Token
  ( -- * Tokenized
    Tokenized (..)
  , satisfy
  , tokens
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
  :: (Choice p, Cochoice p, Tokenized token (p token token))
  => (token -> Bool) -> p token token
satisfy f = satisfied f >?< anyToken

tokens
  :: ( AsEmpty s, Cons s s a a
     , Monoidal p, Choice p
     , Tokenized a (p a a)
     )
  => [a] -> p s s
tokens = foldr ((>:<) . token) asEmpty

terminator
  :: (Foldable f, Eq a, Monoidal p, Cochoice p, Tokenized token (p a a))
  => f a -> p () ()
terminator = foldr (\a -> (only a ?< anyToken *>)) oneP

{- |
`oneLike` consumes one token
of a given token's category while parsing,
and produces the given token while printing.
-}
oneLike
  :: forall token p. (Profunctor p, Tokenized token (p token token))
  => token -> p () ()
oneLike a = dimap (const a) (\(_::token) -> ()) (asIn (categorize a))

{- |
`manyLike` consumes zero or more tokens
of a given token's category while parsing,
and produces no tokens printing.
-}
manyLike
  :: forall token p. (Distributor p, Tokenized token (p token token))
  => token -> p () ()
manyLike a = dimap (\_ -> []::[token]) (\(_::[token]) -> ())
  (manyP (asIn (categorize a)))

{- |
`optLike` consumes zero or more tokens
of a given token's category while parsing,
and produces the given token while printing.
-}
optLike
  :: forall token p. (Distributor p, Tokenized token (p token token))
  => token -> p () ()
optLike a = dimap (\_ -> [a]::[token]) (\(_::[token]) -> ())
  (manyP (asIn (categorize a)))

{- |
`someLike` consumes one or more tokens
of a given token's category while parsing,
and produces the given token while printing.
-}
someLike
  :: forall token p. (Distributor p, Tokenized token (p token token))
  => token -> p () ()
someLike a = dimap (const (a, [] :: [token])) (\(_::token, _::[token]) -> ())
  (asIn (categorize a) >*< manyP (asIn (categorize a)))
