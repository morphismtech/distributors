{-|
Module      : Data.Profunctor.Do.Bond
Description : monadic pair-bonding do-notation
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Data.Profunctor.Do.Bond
  ( -- *
    (>>=)
  , (>>)
  , fail
  , return
  ) where

import Data.Profunctor (Profunctor (dimap))
import Data.Profunctor.Do.Polyadic.Bind (fail)
import Data.Profunctor.Monadic (Monadic (bondM))
import Prelude hiding ((>>), (>>=), fail)

(>>=) :: Monadic m p => p m a a -> (a -> p m b c) -> p m (a,b) (a,c)
infixl 1 >>=
(>>=) = flip bondM

(>>) :: Monadic m p => p m () () -> p m b c -> p m b c
infixl 1 >>
x >> y = dimap ((),) snd (x >>= const y)
