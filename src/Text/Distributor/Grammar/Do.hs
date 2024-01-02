{-# LANGUAGE PolyKinds #-}
{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}

module Text.Distributor.Grammar.Do
  ( NT, runNT
  , return, mfix, (>>=), fail
  , FixNT (fixNT)
  ) where

import Control.Lens
import Data.Function
import GHC.Exts
import GHC.OverloadedLabels
import GHC.TypeLits
import Prelude hiding (return, (>>=))
import Text.Distributor.Grammar

class FixNT (s :: [Symbol]) p where
  fixNT :: (p -> p) -> p
instance FixNT '[] p where
  fixNT = fix
instance
  ( KnownSymbol s
  , NonTerminal p
  , ss ~ '[s]
  ) => FixNT '[s] p where
    fixNT = recNonTerminal (symbolVal' @s proxy#)
instance
  ( KnownSymbol s0
  , NonTerminal p0
  , KnownSymbol s1
  , NonTerminal p1
  ) => FixNT '[s0,s1] (p0,p1) where
    fixNT f =
      let
        ~(p0,p1) =
            ( fixNT @'[s0] @p0 (\q -> view _1 (f (q,p1)))
            , fixNT @'[s1] @p1 (\q -> view _2 (f (p0,q)))
            )
      in (p0,p1)
instance
  ( KnownSymbol s0
  , NonTerminal p0
  , KnownSymbol s1
  , NonTerminal p1
  , KnownSymbol s2
  , NonTerminal p2
  ) => FixNT '[s0,s1,s2] (p0,p1,p2) where
    fixNT f =
      let
        ~(p0,p1,p2) =
            ( fixNT @'[s0] @p0 (\q -> view _1 (f (q,p1,p2)))
            , fixNT @'[s1] @p1 (\q -> view _2 (f (p0,q,p2)))
            , fixNT @'[s2] @p2 (\q -> view _3 (f (p0,p1,q)))
            )
      in (p0,p1,p2)

data NT (s :: [Symbol]) a where
  NT :: FixNT s a => {getNT :: a} -> NT s a
instance ('[s0] ~ s1, a0 ~ a1, KnownSymbol s0, NonTerminal a1)
  => IsLabel s0 (a0 -> NT s1 a1) where fromLabel = NT

runNT :: NT '[] a -> a
runNT (NT p) = p

return :: a -> NT '[] a
return = NT

mfix :: forall s a. FixNT s a => (a -> NT s a) -> NT s a
mfix aF = NT (fixNT @s (getNT . aF))

(>>=) :: forall s t a b. FixNT s a => NT s a -> (a -> NT t b) -> NT t b
a >>= f = f (fixNT @s (const (getNT a)))
