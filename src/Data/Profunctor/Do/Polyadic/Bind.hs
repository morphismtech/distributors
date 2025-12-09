{-|
Module      : Data.Profunctor.Do.Polyadic.Bind
Description : polyadic binding do-notation
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Data.Profunctor.Do.Polyadic.Bind
  ( -- *
    (>>=)
  , (>>)
  , fail
  , return
  ) where

import Data.Profunctor.Monadic (Monadic (liftP))
import Data.Profunctor.Polyadic (Polyadic, bindP)
import Prelude hiding ((>>), (>>=), fail)
import qualified Prelude (fail)

(>>=)
  :: Polyadic m p
  => p i j m a b
  -> (b -> p j k m a c)
  -> p i k m a c
infixl 1 >>=
(>>=) = flip bindP

(>>)
  :: Polyadic m p
  => p i j m a b
  -> p j k m a c
  -> p i k m a c
infixl 1 >>
x >> y = x >>= const y

fail
  :: (Monadic m p, MonadFail m)
  => String -> p m a a
fail = liftP . Prelude.fail
