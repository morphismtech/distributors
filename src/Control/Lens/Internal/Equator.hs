module Control.Lens.Internal.Equator
  ( -- * Equator
    Equator  (..)
  ) where

import Control.Lens
import Control.Lens.Grammar.Token
import Control.Lens.Internal.Iso
import Control.Lens.Internal.Prism
import Control.Lens.Internal.Profunctor
import Control.Lens.PartialIso

class Equator a b p | p -> a, p -> b where
  equate :: p a b
  default equate :: Tokenized token (p a b) => p a b
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
