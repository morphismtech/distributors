module Control.Lens.Internal.Equator
  ( -- *
    Equator  (..)
  , Equator'
  , equator
  , Identical (..)
  ) where

import Control.Lens
import Control.Lens.Grammar.Token
import Control.Lens.Internal.Iso
import Control.Lens.Internal.Prism
import Control.Lens.Internal.Profunctor
import Control.Lens.PartialIso
import Data.Profunctor
import Data.Profunctor.Monoidal

class Equator a b p | p -> a, p -> b where
  equate :: p a b
  default equate :: (Tokenizor token p, a ~ token, b ~ token) => p a b
  equate = anyToken
instance Equator a b (Identical a b) where equate = Identical
instance Equator a b (Exchange a b) where
  equate = Exchange id id
instance Equator a b (Market a b) where
  equate = Market id Right
instance Equator a b (PartialExchange a b) where
  equate = PartialExchange Just Just
instance (Equator a b p, Profunctor p, Applicative f)
  => Equator a b (WrappedPafb f p) where
    equate = WrapPafb (rmap pure equate)

type Equator' a p = (Eq a, Equator a a p, Monoidal p, Cochoice p)

equator :: Equator' a p => [a] -> p () ()
equator [] = oneP
equator (a:as) = only a ?< equate *> equator as
