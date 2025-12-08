{-|
Module      : Data.Profunctor.Polyadic.Do
Description : polyadic do-notation
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Data.Profunctor.Do.Polyadic
  ( -- *
    (>>=)
  , (>>)
  , fail
  , return
  ) where

import Control.Monad.Fix
import Data.Profunctor
import Data.Profunctor.Monadic
import Prelude hiding ((>>), (>>=), fail)
import qualified Prelude

(>>=)
  :: (Polyadic m p, forall x. MonadFix (p i i m x))
  => p i i m a a -> (a -> p i j m b c) -> p i j m b c
x >>= f = composeP (fmap f (mfix (\a -> lmap (const a) x)))

(>>)
  :: (Polyadic m p, forall x. MonadFix (p i i m x))
  => p i i m a a -> p i j m b c -> p i j m b c
infixl 1 >>
x >> y = x >>= (\_ -> y)

fail
  :: (Polyadic m p, MonadFail m)
  => String
  -> p i i m a b
fail = liftP . Prelude.fail
