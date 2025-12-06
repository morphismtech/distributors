{-|
Module      : Data.Profunctor.Polyadic.Do
Description : polyadic do-notation
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Data.Profunctor.Polyadic.Do
  ( -- *
    (>>=)
  , (>>)
  , fail
  , return
  ) where

import Data.Profunctor.Monadic
import Prelude hiding ((>>), (>>=), fail)
import qualified Prelude

(>>=)
  :: Polyadic m p
  => p i j m a b -> (b -> p j k m a c) -> p i k m a c
x >>= f = composeP (fmap f x)

(>>)
  :: Polyadic m p
  => p i j m a b -> p j k m a c -> p i k m a c
x >> y = x >>= (\_ -> y)

fail
  :: (Polyadic m p, MonadFail m)
  => String
  -> p i i m a b
fail = liftP . Prelude.fail
