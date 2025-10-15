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
  , cloneMonochrome
  , withMonochrome
  , printM
  , parseM
  , Monochromatic (..)
  , runMonochromatic
  ) where

import Control.Lens
import Data.Profunctor.Distributor
import Data.Profunctor.Monadic

type Monochrome m s t a b =
  forall p. Monadic p => p m a (m b) -> p m s (m t)

type AMonochrome m s t a b =
  Monochromatic a b m a (m b) -> Monochromatic a b m s (m t)

printM :: Monad m => AMonochrome m s t a b -> (a -> m (b, x -> x)) -> s -> m (t, x -> x)
printM mon = runLintor . mapMonochrome mon . Lintor

parseM :: Monad m => AMonochrome m s t a b -> (x -> m (b, x)) -> x -> m (t, x)
parseM mon = runParsor . mapMonochrome mon . Parsor

mapMonochrome
  :: (Monadic p, Monad m)
  => AMonochrome m s t a b
  -> p m a b -> p m s t
mapMonochrome mon p = withMonochrome mon $ \f -> lmap f p

cloneMonochrome :: Monad m => AMonochrome m s t a b -> Monochrome m s t a b
cloneMonochrome mon = unwrapMonadic . mapMonochrome mon . WrapMonadic

withMonochrome
  :: (Monadic p, Monad m)
  => AMonochrome m s t a b
  -> ((s -> a) -> p m x b) -> p m x t
withMonochrome mon = unMonochromatic (joinP (mon (return <$> anyToken)))

newtype Monochromatic a b m s t = Monochromatic
  {unMonochromatic :: forall p x. Monadic p => ((s -> a) -> p m x b) -> p m x t}
instance Tokenized a b (Monochromatic a b m) where
  anyToken = Monochromatic ($ id)
instance Monad m => Profunctor (Monochromatic a b m) where
  dimap f g (Monochromatic k) =
    Monochromatic (fmap g . k . (. (. f)))
instance Monad m => Functor (Monochromatic a b m s) where fmap = rmap
instance Monad m => Applicative (Monochromatic a b m s) where
  pure t = Monochromatic (pure (pure t))
  Monochromatic x <*> Monochromatic y = Monochromatic (liftA2 (<*>) x y)
instance Monad m => Monad (Monochromatic a b m s) where
  return = pure
  Monochromatic act1 >>= act2 = Monochromatic $ \ctx -> do
    c <- act1 ctx
    unMonochromatic (act2 c) ctx
instance Monadic (Monochromatic a b) where
  joinP (Monochromatic act) = Monochromatic (joinP . act)

runMonochromatic
  :: (Monadic p, Monad m)
  => Monochromatic a b m s t -> p m a b -> p m s t
runMonochromatic (Monochromatic k) p = k $ \f -> lmap f p
