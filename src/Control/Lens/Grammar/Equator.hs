module Control.Lens.Grammar.Equator
  ( -- *
    Equator (..)
  , is
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

class Equator i j p | p -> i, p -> i where
  equate :: p i j
  default equate :: (Tokenizor a p, i ~ a, j ~ a) => p i j
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

is
  :: (Monoidal p, Cochoice p, Equator a a p, Eq a)
  => [a] -> p () ()
is [] = oneP
is (a:as) = only a ?< equate *> is as
