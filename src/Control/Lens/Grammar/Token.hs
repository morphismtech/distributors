module Control.Lens.Grammar.Token
  ( -- * Token
    Categorized (..)
  , Tokenized (..)
  , satisfy
  , tokens
  , Tokenizor
    -- * Like
  , oneLike
  , manyLike
  , optLike
  , someLike
    -- * Unicode
  , GeneralCategory (..)
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.PartialIso
import Data.Char
import Data.Profunctor
import Data.Profunctor.Distributor
import Data.Profunctor.Monoidal
import Data.Word

class (Eq token, Eq (Categorize token)) => Categorized token where
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

class Categorized (Token p) => Tokenized p where
  type Token p

  anyToken :: p

  noToken :: p
  default noToken :: (p ~ f (Token p), Alternative f) => p
  noToken = empty

  token :: Token p -> p
  default token
    :: (p ~ q (Token p) (Token p), Choice q, Cochoice q)
    => Token p -> p
  token = satisfy . token

  notToken :: Token p -> p
  default notToken
    :: (p ~ q (Token p) (Token p), Choice q, Cochoice q)
    => Token p -> p
  notToken = satisfy . notToken

  oneOf :: [Token p] -> p
  default oneOf
    :: (p ~ q (Token p) (Token p), Choice q, Cochoice q)
    => [Token p] -> p
  oneOf = satisfy . oneOf

  notOneOf :: [Token p] -> p
  default notOneOf
    :: (p ~ q (Token p) (Token p), Choice q, Cochoice q)
    => [Token p] -> p
  notOneOf = satisfy . notOneOf

  asIn :: Categorize (Token p) -> p
  default asIn
    :: (p ~ q (Token p) (Token p), Choice q, Cochoice q)
    => Categorize (Token p) -> p
  asIn = satisfy . asIn

  notAsIn :: Categorize (Token p) -> p
  default notAsIn
    :: (p ~ q (Token p) (Token p), Choice q, Cochoice q)
    => Categorize (Token p) -> p
  notAsIn = satisfy . notAsIn

instance Categorized token => Tokenized (token -> Bool) where
  type Token (token -> Bool) = token
  anyToken _ = True
  noToken _ = False
  token = (==)
  notToken = (/=)
  oneOf = flip elem
  notOneOf = flip notElem
  asIn = lmap categorize . (==)
  notAsIn = lmap categorize . (/=)

satisfy
  :: (Choice p, Cochoice p, Tokenizor token p)
  => (token -> Bool) -> p token token
satisfy f = satisfied f >?< anyToken

type Tokenizor token p =
  (Tokenized (p token token), Token (p token token) ~ token)

tokens
  :: ( AsEmpty s, Cons s s token token
     , Monoidal p, Choice p, Tokenizor token p
     )
  => [token] -> p s s
tokens [] = asEmpty
tokens (a:as) = token a >:< tokens as

{- |
`oneLike` consumes one token
of a given token's category while parsing,
and produces the given token while printing.
-}
oneLike
  :: forall token p. (Profunctor p, Tokenizor token p)
  => token -> p () ()
oneLike a = dimap (\_ -> a) (\(_::token) -> ()) (asIn (categorize a))

{- |
`manyLike` consumes zero or more tokens
of a given token's category while parsing,
and produces no tokens printing.
-}
manyLike
  :: forall token p. (Distributor p, Tokenizor token p)
  => token -> p () ()
manyLike a = dimap (\_ -> []::[token]) (\(_::[token]) -> ())
  (manyP (asIn (categorize a)))

{- |
`optLike` consumes zero or more tokens
of a given token's category while parsing,
and produces the given token while printing.
-}
optLike
  :: forall token p. (Distributor p, Tokenizor token p)
  => token -> p () ()
optLike a = dimap (\_ -> [a]::[token]) (\(_::[token]) -> ())
  (manyP (asIn (categorize a)))

{- |
`someLike` accepts one or more tokens
of a given token's category while parsing,
and produces the given token while printing.
-}
someLike
  :: forall token p. (Distributor p, Tokenizor token p)
  => token -> p () ()
someLike a = dimap (\_ -> (a,[]::[token])) (\(_::token, _::[token]) -> ())
  (asIn (categorize a) >*< manyP (asIn (categorize a)))
