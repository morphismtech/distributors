{- |
Module      : Control.Lens.Monochrome
Description : Monochromes
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Control.Lens.Monochrome
  ( Monochrome
  , AMonochrome
  , mapMonochrome
  , withMonochrome
  , Monochromatic (..)
  ) where

import Control.Lens
import Control.Monad
import Data.Profunctor.Distributor

type Monochrome m s t a b =
  forall p. Monadic p => p m a (m b) -> p m s (m t)

type AMonochrome m s t a b =
  Monochromatic a b m a (m b) -> Monochromatic a b m s (m t)

mapMonochrome :: (Monadic p, Monad m) => Monochrome m s t a b -> p m a b -> p m s t
mapMonochrome mon = joinP . mon . fmap return

withMonochrome :: Monad m => AMonochrome m s t a b -> ((s -> a) -> m b) -> m t
withMonochrome mon = unMonochromatic (joinP (mon (return <$> anyToken)))

newtype Monochromatic a b m s t = Monochromatic
  {unMonochromatic :: ((s -> a) -> m b) -> m t}
instance Tokenized a b (Monochromatic a b m) where
  anyToken = Monochromatic ($ id)
instance Functor m => Profunctor (Monochromatic a b m) where
  dimap f g (Monochromatic k) =
    Monochromatic (fmap g . k . (. (. f)))
instance Functor m => Functor (Monochromatic a b m s) where fmap = rmap
instance Applicative m => Applicative (Monochromatic a b m s) where
  pure t = Monochromatic (pure (pure t))
  Monochromatic x <*> Monochromatic y = Monochromatic (liftA2 (<*>) x y)
instance Monad m => Monad (Monochromatic a b m s) where
  return = pure
  Monochromatic act1 >>= act2 = Monochromatic $ \ctx -> do
    c <- act1 ctx
    unMonochromatic (act2 c) ctx
instance Monadic (Monochromatic a b) where
  joinP (Monochromatic act) = Monochromatic (join . act)
