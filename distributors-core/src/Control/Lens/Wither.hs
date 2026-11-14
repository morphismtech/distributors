{- |
Module      : Control.Lens.Wither
Description : withers
Copyright   : (C) 2026 - Eitan Chatav
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
  , Altar (..)
    -- * Combinators
  , cloneWither
  , withered
  , filtraversed
  , filterOf
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.Internal.Context
import Data.Profunctor.Rep
import Data.Profunctor.Sieve
import Prelude hiding (filter)
import Witherable

-- $setup
-- >>> import Control.Applicative (Alternative (..))
-- >>> import Control.Lens
-- >>> import Control.Lens.PartialIso (partialIso, withPartialIso)

{- | `Wither`s extend `Control.Lens.Traversal.Traversal`s by filtering.
`Control.Lens.Traversal.Traversal` ⊂ `Wither`,

so every `Control.Lens.Iso.Iso`, `Control.Lens.Lens.Lens`
& `Control.Lens.Prism.Prism` is a `Wither` too.
-}
type Wither s t a b = forall f. Alternative f => (a -> f b) -> s -> f t

{- | `AWither` is monomorphically a `Wither`.

> prop> Wither s t a b ⊂ AWither s t a b
-}
type AWither s t a b = (a -> Altar a b b) -> s -> Altar a b t

{- | Clone `AWither` so that you can reuse the same
monomorphically typed `Wither` for different purposes.
-}
cloneWither :: AWither s t a b -> Wither s t a b
cloneWither w f = (\g z -> runAltar z g) f . w sell

{- | Construct a `Wither` for a `Witherable`,
dropping each element whose action fails, by `optional`.

A `Control.Lens.Prism.Prism` passes a mismatch through,
so it filters nothing in a `Wither`. Penner's @witherPrism@
makes it fail instead, by `empty`, so that `withered` drops it.

>>> :{
witherPrism
  :: (Choice p, Alternative f)
  => APrism s t a b -> p a (f b) -> p s (f t)
witherPrism prsm = withPrism prsm $ \embed match ->
  dimap match (either (const empty) (fmap embed)) . right'
:}

>>> (withered . witherPrism _Just) (\x -> Just (x + 1)) [Just 1, Nothing, Just 2]
Just [Just 2,Just 3]

With @catMaybes (pure Nothing)@ in place of `empty`, for a `Filterable` @f@,
@witherPrism@ is @withPartialIso prsm partialIso@,
rebuilding a `Control.Lens.PartialIso.PartialIso`
from the partial functions of a `Control.Lens.Prism.Prism`.

>>> (withered . withPartialIso _Just partialIso) (\x -> Just (x + 1)) [Just 1, Nothing, Just 2]
Just [Just 2,Just 3]
-}
withered :: Witherable t => Wither (t a) (t b) a b
withered f = wither (optional . f)

{- |
> prop> withered = filtraversed
-}
filtraversed :: (Filterable t, Traversable t) => Wither (t a) (t b) a b
filtraversed f = fmap catMaybes . traverse (optional . f)

{- | Filter a traversed structure based on a predicate. -}
filterOf :: Alternative m => Wither s t a a -> (a -> Bool) -> s -> m t
filterOf w p s = w guardingp s where
  guardingp a
    | p a = pure a
    | otherwise = empty

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
