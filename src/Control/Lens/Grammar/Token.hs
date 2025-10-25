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

import Control.Lens
import Control.Lens.PartialIso
import Data.Char
import Data.Profunctor
import Data.Profunctor.Distributor
import Data.Word

class (Eq a, Eq (Categorize a)) => Categorized a where
  type Categorize a
  type Categorize a = ()
  categorize :: a -> Categorize a
  default categorize :: Categorize a ~ () => a -> Categorize a
  categorize _ = ()
instance Categorized Char where
  type Categorize Char = GeneralCategory
  categorize = generalCategory
instance Categorized Word8
instance Categorized ()

class Categorized (Token p) => Tokenized p where
  type Token p

  anyToken :: p

  token :: Token p -> p
  default token
    :: (p ~ q (Token p) (Token p), Choice q, Cochoice q)
    => Token p -> p
  token = satisfy . token

  oneOf :: Foldable f => f (Token p) -> p
  default oneOf
    :: (p ~ q (Token p) (Token p), Choice q, Cochoice q)
    => Foldable f => f (Token p) -> p
  oneOf = satisfy . oneOf

  notOneOf :: Foldable f => f (Token p) -> p
  default notOneOf
    :: (p ~ q (Token p) (Token p), Choice q, Cochoice q)
    => Foldable f => f (Token p) -> p
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

instance Categorized c => Tokenized (c -> Bool) where
  type Token (c -> Bool) = c
  anyToken _ = True
  token = (==)
  oneOf = flip elem
  notOneOf = flip notElem
  asIn = lmap categorize . (==)
  notAsIn = lmap categorize . (/=)

satisfy
  :: (Choice p, Cochoice p, Tokenizor a p)
  => (a -> Bool) -> p a a
satisfy f = satisfied f >?< anyToken

type Tokenizor a p = (Tokenized (p a a), Token (p a a) ~ a)

tokens
  :: ( AsEmpty s
     , Cons s s a a
     , Monoidal p
     , Choice p
     , Tokenizor a p
     )
  => [a]
  -> p s s
tokens [] = asEmpty
tokens (a:as) = token a >:< tokens as

{- |
`oneLike` consumes one token
of a given token's category while parsing,
and produces the given token while printing.
-}
oneLike :: forall a p. (Profunctor p, Tokenizor a p) => a -> p () ()
oneLike a = dimap (\_ -> a) (\(_::a) -> ()) (asIn (categorize a))

{- |
`manyLike` consumes zero or more tokens
of a given token's category while parsing,
and produces no tokens printing.
-}
manyLike :: forall a p. (Distributor p, Tokenizor a p) => a -> p () ()
manyLike a = dimap (\_ -> []::[a]) (\(_::[a]) -> ())
  (manyP (asIn (categorize a)))

{- |
`optLike` consumes zero or more tokens
of a given token's category while parsing,
and produces the given token while printing.
-}
optLike :: forall a p. (Distributor p, Tokenizor a p) => a -> p () ()
optLike a = dimap (\_ -> [a]::[a]) (\(_::[a]) -> ())
  (manyP (asIn (categorize a)))

{- |
`someLike` accepts one or more tokens
of a given token's category while parsing,
and produces the given token while printing.
-}
someLike :: forall a p. (Distributor p, Tokenizor a p) => a -> p () ()
someLike a = dimap (\_ -> (a,[]::[a])) (\(_::a, _::[a]) -> ())
  (asIn (categorize a) >*< manyP (asIn (categorize a)))
