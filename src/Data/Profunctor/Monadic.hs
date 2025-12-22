{-|
Module      : Data.Profunctor.Monadic
Description : monadic profunctors
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Data.Profunctor.Monadic
  ( Monadic (..)
  , bondP
  ) where

import Control.Category
import Control.Arrow
import Control.Lens
import Data.Profunctor
import Prelude hiding (id, (.))

class
  ( Profunctor (p m)
  , forall x. Monad (p m x)
  ) => Monadic m p where
  liftP :: m b -> p m a b

instance Monad m => Monadic m Kleisli where
  liftP = Kleisli . return
instance Monad m => Monadic m Star where
  liftP = Star . return

bondP :: Monadic m p => p m a b -> (b -> p m c d) -> p m (a,c) (b,d)
bondP p f = do
  b <- lmap fst p
  d <- lmap snd (f b)
  return (b,d)
