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

  inClass :: [Token p] -> p
  default inClass
    :: (p ~ q (Token p) (Token p), Choice q, Cochoice q)
    => [Token p] -> p
  inClass = satisfy . inClass

  notInClass :: [Token p] -> p
  default notInClass
    :: (p ~ q (Token p) (Token p), Choice q, Cochoice q)
    => [Token p] -> p
  notInClass = satisfy . notInClass

  inCategory :: Categorize (Token p) -> p
  default inCategory
    :: (p ~ q (Token p) (Token p), Choice q, Cochoice q)
    => Categorize (Token p) -> p
  inCategory = satisfy . inCategory

  notInCategory :: Categorize (Token p) -> p
  default notInCategory
    :: (p ~ q (Token p) (Token p), Choice q, Cochoice q)
    => Categorize (Token p) -> p
  notInCategory = satisfy . notInCategory

instance Categorized c => Tokenized (c -> Bool) where
  type Token (c -> Bool) = c
  anyToken _ = True
  token = (==)
  inClass = flip elem
  notInClass = flip notElem
  inCategory = lmap categorize . (==)
  notInCategory = lmap categorize . (/=)

satisfy
  :: ( Choice q, Cochoice q
     , Tokenized p, p ~ q (Token p) (Token p)
     )
  => (Token p -> Bool) -> p
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
oneLike :: forall c p. (Profunctor p, Tokenizor c p) => c -> p () ()
oneLike c = dimap (\_ -> c) (\(_::c) -> ()) (inCategory (categorize c))

{- |
`manyLike` consumes zero or more tokens
of a given token's category while parsing,
and produces no tokens printing.
-}
manyLike :: forall c p. (Distributor p, Tokenizor c p) => c -> p () ()
manyLike c = dimap (\_ -> []::[c]) (\(_::[c]) -> ())
  (manyP (inCategory (categorize c)))

{- |
`optLike` consumes zero or more tokens
of a given token's category while parsing,
and produces the given token while printing.
-}
optLike :: forall c p. (Distributor p, Tokenizor c p) => c -> p () ()
optLike c = dimap (\_ -> [c]::[c]) (\(_::[c]) -> ())
  (manyP (inCategory (categorize c)))

{- |
`someLike` accepts one or more tokens
of a given token's category while parsing,
and produces the given token while printing.
-}
someLike :: forall c p. (Distributor p, Tokenizor c p) => c -> p () ()
someLike c = dimap (\_ -> (c,[]::[c])) (\(_::c, _::[c]) -> ())
  (inCategory (categorize c) >*< manyP (inCategory (categorize c)))
