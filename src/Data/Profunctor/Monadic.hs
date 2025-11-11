{-|
Module      : Data.Profunctor.Monadic
Description : monadic profunctors
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

{-# LANGUAGE PolyKinds #-}

module Data.Profunctor.Monadic
  ( Monadic (..)
  , Polyadic (..)
  , Tetradic (..)
  , WrappedMonadic (..)
  , WrappedPolyadic (..)
  , TaggedP (..)
  , UntaggedT (..)
  , UntaggedC (..)
  ) where

import Control.Category
import Control.Comonad
import Control.Arrow
import Control.Monad
import Control.Monad.State
import Control.Monad.Trans.Indexed
import Data.Profunctor
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

class
  ( forall i j. Profunctor (p i j m)
  , forall i j x. Functor (p i j m x)
  , forall i. Monadic m (p i i)
  ) => Polyadic m p where
  composeP :: p i j m a (p j k m a b) -> p i k m a b

class (forall i j. Profunctor (p i j f)) => Tetradic f p where

  tetramap
    :: (h -> i) -> (j -> k)
    -> (s -> a) -> (b -> t)
    -> p i j f a b -> p h k f s t
  tetramap f1 f2 f3 f4 = dimapT f1 f2 . dimap f3 f4

  dimapT
    :: (h -> i) -> (j -> k)
    -> p i j f a b -> p h k f a b
  dimapT f1 f2 = tetramap f1 f2 id id

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

newtype WrappedPolyadic p i j m a b =
  WrapPolyadic {unwrapPolyadic :: p i j m a (m b)}
instance (Polyadic m p, Monad m)
  => Functor (WrappedPolyadic p i j m a) where
  fmap = rmap
instance (Polyadic m p, Monad m)
  => Applicative (WrappedPolyadic p i i m a) where
  pure x = WrapPolyadic $ pure (pure x)
  WrapPolyadic p1 <*> WrapPolyadic p2 =
      WrapPolyadic $ liftA2 (<*>) p1 p2
instance (Polyadic m p, Monad m)
  => Monad (WrappedPolyadic p i i m a) where
  return = pure
  WrapPolyadic p >>= f = WrapPolyadic $ do
    b <- joinP p
    unwrapPolyadic (f b)
instance (Polyadic m p, Monad m)
  => Profunctor (WrappedPolyadic p i j m) where
  dimap f g = WrapPolyadic . dimap f (fmap g) . unwrapPolyadic
instance (Monad m, Polyadic m p)
  => Monadic m (WrappedPolyadic p i i) where
  joinP = WrapPolyadic . joinP . unwrapPolyadic
instance (Monad m, Polyadic m p) => Polyadic m (WrappedPolyadic p) where
  composeP
    = WrapPolyadic . composeP
    . fmap unwrapPolyadic . composeP
    . fmap liftP . unwrapPolyadic

newtype TaggedP t i j f a b = TagP {untagP :: t i j f b}
  deriving newtype (Functor, Applicative, Monad)
instance Functor (t i j f) => Profunctor (TaggedP t i j f) where
  dimap _ f = TagP . fmap f . untagP
instance (Monad m, MonadTrans (t i j))
  => Monadic m (TaggedP t i j) where
  liftP = TagP . lift
instance (Monad m, IxMonadTrans t)
  => Polyadic m (TaggedP t) where
  composeP = TagP . joinIx . fmap untagP . untagP

newtype UntaggedT p a i j f b = UntagT {tagT :: p i j f a b}
  deriving newtype (Functor, Applicative, Monad)
instance (forall m. Monad m => Monadic m (p i j))
  => MonadTrans (UntaggedT p a i j) where
  lift = UntagT . liftP
instance (forall m. Monad m => Polyadic m p)
  => IxMonadTrans (UntaggedT p a) where
  joinIx = UntagT . composeP . fmap tagT . tagT

newtype UntaggedC p a b f i j = UntagC {tagC :: p i j f a b}
instance (Tetradic f p, Functor f) => Tetradic f (UntaggedC p) where
  tetramap f1 f2 f3 f4 = UntagC . tetramap f3 f4 f1 f2 . tagC
instance (Tetradic f p, Functor f) => Profunctor (UntaggedC p a b f) where
  dimap f g = UntagC . dimapT f g . tagC
instance (Tetradic f p, Functor f) => Functor (UntaggedC p a b f i) where
  fmap = rmap
instance (Polyadic m p, Monoid b) => Category (UntaggedC p a b m) where
  id = UntagC (pure mempty)
  UntagC g . UntagC f = UntagC (composeP (fmap (\b -> fmap (<> b) g) f))
instance (Polyadic m p, Monad m, Monoid b)
  => Semigroup (UntaggedC p a b m i i) where (<>) = (>>>)
instance (Polyadic m p, Monad m, Monoid b)
  => Monoid (UntaggedC p a b m i i) where mempty = id
