{-# LANGUAGE PolyKinds #-}
{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}

module Text.Distributor.Grammar.Do
  ( return, mfix, (>>=), fail
  , FixNT (fixNT)
  ) where

import Data.Function
import Prelude hiding ((>>=))
import Text.Distributor.Grammar

mfix :: forall s a. FixNT s a => (a -> NT s a) -> NT s a
mfix aF = NT (fixNT @s (runNT . aF))

(>>=) :: forall s t a b. FixNT s a => NT s a -> (a -> NT t b) -> NT t b
a >>= f = f (fixNT @s (const (runNT a)))
