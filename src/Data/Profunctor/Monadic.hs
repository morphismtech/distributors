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
  , liftedP
  , joined
  , joinedP
  , bound
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
  joinP :: p m a (m b) -> p m a b
  joinP = join . fmap liftP
  liftP :: m b -> p m a b
  liftP = joinP . return
instance Monad m => Monadic m Kleisli where
  liftP = Kleisli . return
instance Monad m => Monadic m Star where
  liftP = Star . return
instance Comonad w => Monadic w Costar where
  liftP = Costar . return . extract

monochrome_
  :: (Monadic m p, Applicative m)
  => p m a b -> Optic (p m) m a b () ()
monochrome_ = monochrome . (*<)

monochrome
  :: (Monadic m p, Applicative m)
  => (p m a b -> p m s t) -> Optic (p m) m s t a b
monochrome f = fmap pure . f . joinP

withMonochrome_
  :: (Monadic m p, Applicative m)
  => Optic (p m) m a b () () -> p m a b
withMonochrome_ f = withMonochrome f oneP

withMonochrome
  :: (Monadic m p, Applicative m)
  => Optic (p m) m s t a b -> p m a b -> p m s t
withMonochrome f = joinP . f . fmap pure

liftedP :: (Monadic m p, Applicative m) => m b -> Optic (p m) m a b () ()
liftedP m = monochrome_ (liftP m)

joinedP :: (Monadic m p, Applicative m) => Optic (p m) m a b a (m b)
joinedP = monochrome joinP

joined :: (Monadic m p, Applicative m) => Optic (p m) m a b a (p m a b)
joined = monochrome join

bound
  :: (Monadic m p, Applicative m)
  => (b -> Optic (p m) m a c a ()) -> Optic (p m) m a c a b
bound f = monochrome $ \p -> do
  b <- p
  withMonochrome (f b) (return ())

newtype WrappedMonadic p m a b = WrapMonadic {unwrapMonadic :: p m a (m b)}
instance (Monadic m p, Monad m) => Functor (WrappedMonadic p m a) where
  fmap = rmap
instance (Monadic m p, Monad m) => Applicative (WrappedMonadic p m a) where
  pure x = WrapMonadic $ pure (pure x)
  WrapMonadic p1 <*> WrapMonadic p2 = WrapMonadic $ liftA2 (<*>) p1 p2
instance (Monadic m p, Monad m) => Monad (WrappedMonadic p m a) where
  return = pure
  WrapMonadic p >>= f = WrapMonadic $ do
    b <- joinP p
    unwrapMonadic (f b)
instance (Monadic m p, Monad m) => Profunctor (WrappedMonadic p m) where
  dimap f g (WrapMonadic p) = WrapMonadic $ dimap f (fmap g) p
instance (Monad m, Monadic m p) => Monadic m (WrappedMonadic p) where
  joinP (WrapMonadic p) = WrapMonadic (joinP p)
