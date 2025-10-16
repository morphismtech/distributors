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
  , Tetrafunctor (..)
  , WrappedMonadic (..)
  , TaggedP (..)
  , TetraT (..)
  , TetraC (..)
  ) where

import Control.Category
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Indexed
import Data.Profunctor
import Data.Profunctor.Distributor
import Prelude hiding (id, (.))

class
  ( forall m. Monad m => Profunctor (p m)
  , forall m x. Monad m => Monad (p m x)
  ) => Monadic p where
  joinP :: Monad m => p m a (m b) -> p m a b
instance Monadic (Parsor s s) where
  joinP (Parsor p) = Parsor $ \s -> do
    (mb, s') <- p s
    b <- mb
    return (b, s')
instance Monadic (Lintor s s) where
  joinP (Lintor p) = Lintor $ \a -> do
    (mb, q) <- p a
    b <- mb
    return (b, q)

class
  ( forall i j. i ~ j => Monadic (p i j)
  , forall i j m a. Monad m => Functor (p i j m a)
  ) => Polyadic p where
  composeP :: Monad m => p i j m a (p j k m a b) -> p i k m a b
instance Polyadic Parsor where
  composeP (Parsor p) = Parsor $ \s -> do
    (mb, s') <- p s
    runParsor mb s'
instance Polyadic Lintor where
  composeP (Lintor p) = Lintor $ \ctx -> do
    (Lintor p', ij) <- p ctx
    (b, jk) <- p' ctx
    return (b, jk . ij)

class (forall f i j. Functor f => Profunctor (p i j f))
  => Tetrafunctor p where
    dimapIx
      :: Functor f
      => (h -> i) -> (j -> k)
      -> p i j f a b -> p h k f a b
    tetramap
      :: Functor f
      => (h -> i) -> (j -> k)
      -> (s -> a) -> (b -> t)
      -> p i j f a b -> p h k f s t
    tetramap f1 f2 f3 f4 = dimapIx f1 f2 . dimap f3 f4
instance Tetrafunctor Printor where
  dimapIx f g (Printor p) = Printor (fmap (dimap f g) . p)
instance Tetrafunctor Parsor where
  dimapIx f g (Parsor p) = Parsor (fmap (fmap g) . p . f)
instance Tetrafunctor Lintor where
  dimapIx f g (Lintor p) = Lintor (fmap (second' (dimap f g)) . p)

newtype WrappedMonadic p m a b = WrapMonadic {unwrapMonadic :: p m a (m b)}
instance (Monadic p, Monad m) => Functor (WrappedMonadic p m a) where
  fmap = rmap
instance (Monadic p, Monad m) => Applicative (WrappedMonadic p m a) where
  pure x = WrapMonadic $ pure (pure x)
  WrapMonadic p1 <*> WrapMonadic p2 = WrapMonadic $ liftA2 (<*>) p1 p2
instance (Monadic p, Monad m) => Monad (WrappedMonadic p m a) where
  return = pure
  WrapMonadic p >>= f = WrapMonadic $ do
    b <- joinP p
    unwrapMonadic (f b)
instance (Monadic p, Monad m) => Profunctor (WrappedMonadic p m) where
  dimap f g (WrapMonadic p) = WrapMonadic $ dimap f (fmap g) p
instance Monadic p => Monadic (WrappedMonadic p) where
  joinP (WrapMonadic p) = WrapMonadic (joinP p)

newtype TaggedP t i j f a b = TaggedP {runTaggedP :: t i j f b}
  deriving newtype (Functor, Applicative, Monad)
instance Functor (t i j f) => Profunctor (TaggedP t i j f) where
  dimap _ f = TaggedP . fmap f . runTaggedP
instance MonadTrans (t i j) => Monadic (TaggedP t i j) where
  joinP = TaggedP . join . fmap lift . runTaggedP
instance IxMonadTrans t => Polyadic (TaggedP t) where
  composeP = TaggedP . joinIx . fmap runTaggedP . runTaggedP

newtype TetraT p a i j f b = TetraT {runTetraT :: p i j f a b}
  deriving newtype (Functor, Applicative, Monad)
instance Monadic (p i j) => MonadTrans (TetraT p a i j) where
  lift = TetraT . joinP . return
instance Polyadic p => IxMonadTrans (TetraT p a) where
  joinIx = TetraT . composeP . fmap runTetraT . runTetraT

newtype TetraC p f a b i j = TetraC {runTetraC :: p i j f a b}
instance (Tetrafunctor p, Functor f) => Profunctor (TetraC p f a b) where
  dimap f g = TetraC . dimapIx f g . runTetraC
instance (Tetrafunctor p, Functor f) => Functor (TetraC p f a b i) where
  fmap = rmap
instance (Polyadic p, Monad m, Monoid b) => Category (TetraC p m a b) where
  id = TetraC (pure mempty)
  TetraC g . TetraC f = TetraC (composeP (fmap (\b -> fmap (<> b) g) f))
