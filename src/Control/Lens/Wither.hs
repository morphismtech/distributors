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
  ( -- * Wither
    Wither
  , AWither
    -- * Combinators
  , cloneWither
  , withered
  , filtraversed
  , filterOf
    -- * Witheroid
  , Witheroid
  , witherPrism
    -- * Altar
  , Altar (..)
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.Internal.Context
import Data.Profunctor.Rep
import Data.Profunctor.Sieve
import Prelude hiding (filter)
import Witherable

{- | `Wither`s extends `Control.Lens.Traversal.Traversal`s by filtering.


Every one of the following is a `Wither`.

* `Control.Lens.Iso.Iso`
* `Control.Lens.Lens.Lens`
* `Control.Lens.Prism.Prism`
* `Control.Lens.Traversal.Traversal`
* `Witheroid`
-}
type Wither s t a b = forall f. Alternative f => (a -> f b) -> s -> f t

{- | If you see `AWither` in a signature for a function,
the function is expecting a `Wither`. -}
type AWither s t a b = (a -> Altar a b b) -> s -> Altar a b t

{- | `Witheroid`s generalize `Wither`s.
Every `Control.Lens.Prism.Prism` is a `Witheroid`.
-}
type Witheroid s t a b = forall p f.
  (Choice p, Alternative f)
    => p a (f b) -> p s (f t)

{- | Clone `AWither` so that you can reuse the same
monomorphically typed `Wither` for different purposes.
-}
cloneWither :: AWither s t a b -> Wither s t a b
cloneWither w f = (\g z -> runAltar z g) f . w sell

{- | Construct a `Wither` for a `Witherable`. -}
withered :: Witherable t => Wither (t a) (t b) a b
withered f = wither (optional . f)

{- |
prop> withered = filtraversed
-}
filtraversed :: (Filterable t, Traversable t) => Wither (t a) (t b) a b
filtraversed f = fmap catMaybes . traverse (optional . f)

{- | Filter a traversed structure based on a predicate. -}
filterOf :: Alternative m => Wither s t a a -> (a -> Bool) -> s -> m t
filterOf w p s = w guardingp s where
  guardingp a
    | p a = pure a
    | otherwise = empty

{- |
`Control.Lens.Prism.Prism`s already capture the idea of success and failure,
but they simply skip the traversal if the prism doesn't match.
Lift prisms into withers such that they'll fail in a way that wither can catch.
-}
witherPrism :: APrism s t a b -> Witheroid s t a b
witherPrism prsm =
  withPrism prsm $ \embed match ->
    dimap match (either (const empty) (fmap embed)) . right'

{- | This is used to characterize `Wither`s. -}
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
