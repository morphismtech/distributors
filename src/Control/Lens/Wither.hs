{- |
Module      : Control.Lens.Wither
Description : withers
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable

See Chris Penner,
[Composable Filters Using Witherable Optics](https://chrispenner.ca/posts/witherable-optics)
-}

module Control.Lens.Wither
  ( Wither
  , Wither'
  , AWither
  , AWither'
  , Witheroid
  , cloneWither
  , withered
  , filtraversed
  , filterOf
  , witherPrism
  , Altar (..)
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.Internal.Context
import Data.Profunctor.Rep
import Data.Profunctor.Sieve
import Prelude hiding (filter)
import Witherable

type Wither s t a b = forall f. Alternative f => (a -> f b) -> s -> f t

type Wither' s a = Wither s s a a

type AWither s t a b = (a -> Altar a b b) -> s -> Altar a b t

type AWither' s a = AWither s s a a

type Witheroid s t a b = forall p f.
  (Choice p, Alternative f)
    => p a (f b) -> p s (f t)

cloneWither :: AWither s t a b -> Wither s t a b
cloneWither w f = (\g z -> runAltar z g) f . w sell

withered :: Witherable t => Wither (t a) (t b) a b
withered f = wither (optional . f)

filtraversed :: (Filterable t, Traversable t) => Wither (t a) (t b) a b
filtraversed f = fmap catMaybes . traverse (optional . f)

filterOf :: Alternative m => Wither s t a a -> (a -> Bool) -> s -> m t
filterOf w p s = w guardingp s where
  guardingp a
    | p a = pure a
    | otherwise = empty

witherPrism :: APrism s t a b -> Witheroid s t a b
witherPrism prsm =
  withPrism prsm $ \embed match ->
    dimap match (either (const empty) (fmap embed)) . right'

newtype Altar a b t = Altar
  { runAltar :: forall f. Alternative f => (a -> f b) -> f t }
instance Functor (Altar a b) where
  fmap f (Altar k) = Altar (fmap f . k)
instance Applicative (Altar a b) where
  pure a = Altar $ const (pure a)
  Altar mf <*> Altar ma = Altar $ liftA2 (<*>) mf ma
instance Alternative (Altar a b) where
  empty = Altar $ const empty
  Altar mx <|> Altar my = Altar $ liftA2 (<|>) mx my
instance Sellable (->) Altar where
  sell
    = cotabulate
    $ \w -> Altar
    $ tabulate
    $ \k -> pure (cosieve k w)
