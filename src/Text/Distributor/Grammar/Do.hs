module Text.Distributor.Grammar.Do
  ( mfix
  , (>>=)
  , return
  ) where

import Data.Coerce
import GHC.Exts
import GHC.TypeLits
import Prelude hiding ((>>=))
import Text.Distributor.Grammar

mfix
  :: forall s a. (KnownSymbol s, NonTerminal a)
  => (a -> NT s a) -> NT s a
mfix aF = return (recNonTerminal (symbolVal' @s proxy#) (coerce . aF))

(>>=)
  :: forall s t a b. (KnownSymbol s, NonTerminal a)
  => NT s a -> (a -> NT t b) -> NT t b
a >>= f = f (nonTerminal (symbolVal' @s proxy#) (coerce a))
