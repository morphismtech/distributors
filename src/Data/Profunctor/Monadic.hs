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
  , monochrome
  , monochrome_
  , withMonochrome
  , withMonochrome_
  ) where

import Control.Applicative
import Control.Category
import Control.Comonad
import Control.Arrow
import Control.Lens
import Control.Monad
import Data.Profunctor
import Data.Profunctor.Monoidal
import Prelude hiding (id, (.))

class
  ( Profunctor (p m)
  , forall x. Monad (p m x)
  ) => Monadic m p where
  liftP :: m b -> p m a b
  bondM :: (a -> p m b c) -> p m a a -> p m (a,b) (a,c)
instance Monad m => Monadic m Kleisli where
  liftP = Kleisli . return
  bondM g (Kleisli f) = Kleisli $ \(x,b) -> do
    y <- f x
    c <- runKleisli (g y) b
    return (y,c)
instance Monad m => Monadic m Star where
  liftP = Star . return
  bondM g (Star f) = Star $ \(x,b) -> do
    y <- f x
    c <- runStar (g y) b
    return (y,c)

monochrome_
  :: (Monadic m p, Applicative m)
  => p m a b -> Optic (p m) m a b () ()
monochrome_ = monochrome . (*<)

monochrome
  :: (Monadic m p, Applicative m)
  => (p m a b -> p m s t) -> Optic (p m) m s t a b
monochrome f = fmap pure . f . join . fmap liftP

withMonochrome_
  :: (Monadic m p, Applicative m)
  => Optic (p m) m a b () () -> p m a b
withMonochrome_ f = withMonochrome f oneP

withMonochrome
  :: (Monadic m p, Applicative m)
  => Optic (p m) m s t a b -> p m a b -> p m s t
withMonochrome f = join . fmap liftP . f . fmap pure
