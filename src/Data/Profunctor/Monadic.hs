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
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Indexed
import Data.Profunctor
import Prelude hiding (id, (.))

class
  ( forall m. Monad m => Profunctor (p m)
  , forall m x. Monad m => Monad (p m x)
  ) => Monadic p where

  joinP :: Monad m => p m a (m b) -> p m a b
  joinP = join . fmap liftP

  liftP :: Monad m => m b -> p m a b
  liftP = joinP . return

-- instance Monadic (Parsor s s) where
--   joinP (Parsor p) = Parsor $ \s -> do
--     (mb, s') <- p s
--     b <- mb
--     return (b, s')
-- instance Monadic (CtxPrintor s s) where
--   joinP (CtxPrintor p) = CtxPrintor $ \a -> do
--     (mb, q) <- p a
--     b <- mb
--     return (b, q)

class
  ( forall i j. i ~ j => Monadic (p i j)
  , forall i j m. Monad m => Profunctor (p i j m)
  , forall i j m a. Monad m => Functor (p i j m a)
  ) => Polyadic p where
  composeP :: Monad m => p i j m a (p j k m a b) -> p i k m a b

-- instance Polyadic Parsor where
--   composeP (Parsor p) = Parsor $ \s -> do
--     (mb, s') <- p s
--     runParsor mb s'
-- instance Polyadic CtxPrintor where
--   composeP (CtxPrintor p) = CtxPrintor $ \ctx -> do
--     (CtxPrintor p', ij) <- p ctx
--     (b, jk) <- p' ctx
--     return (b, jk . ij)

class (forall f i j. Functor f => Profunctor (p i j f))
  => Tetradic p where

    tetramap
      :: Functor f
      => (h -> i) -> (j -> k)
      -> (s -> a) -> (b -> t)
      -> p i j f a b -> p h k f s t
    tetramap f1 f2 f3 f4 = dimapT f1 f2 . dimap f3 f4

    dimapT
      :: Functor f
      => (h -> i) -> (j -> k)
      -> p i j f a b -> p h k f a b
    dimapT f1 f2 = tetramap f1 f2 id id

-- instance Tetradic Printor where
--   dimapT f g (Printor p) = Printor (fmap (dimap f g) . p)
-- instance Tetradic Parsor where
--   dimapT f g (Parsor p) = Parsor (fmap (fmap g) . p . f)
-- instance Tetradic CtxPrintor where
--   dimapT f g (CtxPrintor p) = CtxPrintor (fmap (second' (dimap f g)) . p)

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

newtype WrappedPolyadic p i j m a b = WrapPolyadic {unwrapPolyadic :: p i j m a (m b)}
instance (Polyadic p, Monad m) => Functor (WrappedPolyadic p i j m a) where
  fmap = rmap
instance (Polyadic p, Monad m, i ~ j) => Applicative (WrappedPolyadic p i j m a) where
  pure x = WrapPolyadic $ pure (pure x)
  WrapPolyadic p1 <*> WrapPolyadic p2 = WrapPolyadic $ liftA2 (<*>) p1 p2
instance (Polyadic p, Monad m, i ~ j) => Monad (WrappedPolyadic p i j m a) where
  return = pure
  WrapPolyadic p >>= f = WrapPolyadic $ do
    b <- joinP p
    unwrapPolyadic (f b)
instance (Polyadic p, Monad m) => Profunctor (WrappedPolyadic p i j m) where
  dimap f g = WrapPolyadic . dimap f (fmap g) . unwrapPolyadic
instance (Polyadic p, i ~ j) => Monadic (WrappedPolyadic p i j) where
  joinP = WrapPolyadic . joinP . unwrapPolyadic
instance Polyadic p => Polyadic (WrappedPolyadic p) where
  composeP
    = WrapPolyadic . composeP
    . fmap unwrapPolyadic . composeP
    . fmap liftP . unwrapPolyadic

newtype TaggedP t i j f a b = TagP {untagP :: t i j f b}
  deriving newtype (Functor, Applicative, Monad)
instance Functor (t i j f) => Profunctor (TaggedP t i j f) where
  dimap _ f = TagP . fmap f . untagP
instance MonadTrans (t i j) => Monadic (TaggedP t i j) where
  liftP = TagP . lift
instance IxMonadTrans t => Polyadic (TaggedP t) where
  composeP = TagP . joinIx . fmap untagP . untagP

newtype UntaggedT p a i j f b = UntagT {tagT :: p i j f a b}
  deriving newtype (Functor, Applicative, Monad)
instance Monadic (p i j) => MonadTrans (UntaggedT p a i j) where
  lift = UntagT . liftP
instance Polyadic p => IxMonadTrans (UntaggedT p a) where
  joinIx = UntagT . composeP . fmap tagT . tagT

newtype UntaggedC p a b f i j = UntagC {tagC :: p i j f a b}
instance Tetradic p => Tetradic (UntaggedC p) where
  tetramap f1 f2 f3 f4 = UntagC . tetramap f3 f4 f1 f2 . tagC
instance (Tetradic p, Functor f) => Profunctor (UntaggedC p a b f) where
  dimap f g = UntagC . dimapT f g . tagC
instance (Tetradic p, Functor f) => Functor (UntaggedC p a b f i) where
  fmap = rmap
instance (Polyadic p, Monad m, Monoid b) => Category (UntaggedC p a b m) where
  id = UntagC (pure mempty)
  UntagC g . UntagC f = UntagC (composeP (fmap (\b -> fmap (<> b) g) f))
instance (Polyadic p, Monad m, Monoid b, i ~ j)
  => Semigroup (UntaggedC p a b m i j) where (<>) = (>>>)
instance (Polyadic p, Monad m, Monoid b, i ~ j)
  => Monoid (UntaggedC p a b m i j) where mempty = id
