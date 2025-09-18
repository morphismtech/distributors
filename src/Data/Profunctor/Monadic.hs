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
  ) where

import Data.Profunctor
import Data.Profunctor.Distributor

class
  ( forall m. Monad m => Profunctor (p m)
  , forall m x. Monad m => Monad (p m x)
  ) => Monadic p where
  joinP :: Monad m => p m a (m b) -> p m a b

instance Monadic (Parsor s) where
  joinP (Parsor p) = Parsor $ \s -> do
    (mb, s') <- p s
    b <- mb
    return (b, s')
instance Monadic (Lintor s) where
  joinP (Lintor p) = Lintor $ \a -> do
    (mb, q) <- p a
    b <- mb
    return (b, q)
