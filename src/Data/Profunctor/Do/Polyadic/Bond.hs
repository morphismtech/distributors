{-|
Module      : Data.Profunctor.Do.Polyadic.Bond
Description : polyadic pair-bonding do-notation
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Data.Profunctor.Do.Polyadic.Bond
  ( -- *
    (>>=)
  , (>>)
  , fail
  , return
  ) where

import Data.Profunctor (Profunctor (dimap))
import Data.Profunctor.Do.Polyadic.Bind (fail)
import Data.Profunctor.Polyadic (Polyadic (bondP))
import Prelude hiding ((>>), (>>=), fail)

(>>=)
  :: Polyadic m p
  => p i i m a a
  -> (a -> p i j m b c)
  -> p i j m (a,b) (a,c)
infixl 1 >>=
(>>=) = flip bondP

(>>)
  :: Polyadic m p
  => p i i m () ()
  -> p i j m b c
  -> p i j m b c
infixl 1 >>
x >> y = dimap ((),) snd (x >>= const y)
