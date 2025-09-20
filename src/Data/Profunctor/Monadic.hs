{-|
Module      : Data.Profunctor.Distributor
Description : distributors
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Data.Profunctor.Monadic
  ( Monadic (..)
  , Polyadic (..)
  , WrappedMonadic (..)
  ) where

import Data.Profunctor
import Data.Profunctor.Distributor

class
  ( forall m. Monad m => Profunctor (p m)
  , forall m x. Monad m => Monad (p m x)
  ) => Monadic p where
  joinP :: Monad m => p m a (m b) -> p m a b

class
  ( forall i j. i ~ j => Monadic (p i j)
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
    return (b, jk. ij)

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
