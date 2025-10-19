{-|
Module      : Data.Profunctor.Monadic.Do
Description : overloaded do-notation
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Data.Profunctor.Monadic.Do
  ( -- *
    (>>=)
  , (>>)
  , return
  , fail
  ) where

import Data.Profunctor.Monadic
import Prelude hiding ((>>), (>>=))

(>>=)
  :: (Polyadic p, Monad m)
  => p i j m a b -> (b -> p j k m a c) -> p i k m a c
x >>= f = composeP (fmap f x)

(>>)
  :: (Polyadic p, Monad m)
  => p i j m a b -> p j k m a c -> p i k m a c
x >> y = x >>= (\_ -> y)
