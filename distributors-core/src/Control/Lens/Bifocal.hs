{- |
Module      : Control.Lens.Bifocal
Description : bifocals
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Control.Lens.Bifocal
  ( -- * Bifocal
    Bifocal
  , ABifocal
  , Binocular (..), runBinocular
    -- * Combinators
  , bifocal
  , withBifocal
  , cloneBifocal
  , mapBifocal
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.Internal.Profunctor
import Control.Lens.PartialIso
import Data.Monoid.Disjunctive (DisjunctiveMonoid)
import Data.Profunctor
import Data.Profunctor.Distributor
import Data.Profunctor.Monoidal.Cocartesian
import Data.Profunctor.Filtrator
import Witherable

{- | `Bifocal`s are bidirectional parser optics.
Writing ⊂ for "every one is a",

`Control.Lens.Prismoid.Prismoid` ∪ `Control.Lens.PartialIso.PartialIso` ⊂ `Bifocal`,

so every `Control.Lens.Iso.Iso`, `Control.Lens.Prism.Prism`,
`Control.Lens.PartialIso.filterPrism`, `Control.Lens.Monocle.Monocle`,
`Control.Lens.Comonocle.Comonocle` & `Control.Lens.Diopter.Diopter`
is a `Bifocal` too.

`Bifocal`s are isomorphic to t'Binocular's.
-}
type Bifocal s t a b = forall p f.
  (Alternator p, Applicative f, Filterable f)
    => p a (f b) -> p s (f t)

{- | `ABifocal` is monomorphically a `Bifocal`. -}
type ABifocal s t a b =
  Binocular a b a (Maybe b) -> Binocular a b s (Maybe t)

{- | Build a `Bifocal` from a concrete t'Binocular'. -}
bifocal :: Binocular a b s t -> Bifocal s t a b
bifocal bif = unwrapPafb . runBinocular bif . WrapPafb

{- | Action of `ABifocal` on partial `Distributor`s. -}
mapBifocal
  :: (Alternator p, Filtrator p)
  => ABifocal s t a b -> p a b -> p s t
mapBifocal bif p = withBifocal bif $ \f -> dimapMaybe f Just p

{- | Clone `ABifocal` so that you can reuse the same
monomorphically typed `Bifocal` for different purposes.
-}
cloneBifocal :: ABifocal s t a b -> Bifocal s t a b
cloneBifocal bif = unwrapPafb . mapBifocal bif . WrapPafb

{- | Run `ABifocal` over an `Alternative` & `Filterable`. -}
withBifocal
  :: (Alternative f, Filterable f)
  => ABifocal s t a b -> ((s -> Maybe a) -> f b) -> f t
withBifocal bif = unBinocular (catMaybes (bif (Just <$> Binocular ($ Just))))

{- | t'Binocular' provides an efficient
concrete representation of `Bifocal`s. -}
newtype Binocular a b s t = Binocular
  { unBinocular
      :: forall f. (Alternative f, Filterable f)
      => ((s -> Maybe a) -> f b) -> f t
  }
instance Profunctor (Binocular a b) where
  dimap f g (Binocular k) = Binocular $ fmap g . k . (. (. f))
instance Functor (Binocular a b s) where fmap = rmap
instance Applicative (Binocular a b s) where
  pure t = Binocular (pure (pure t))
  Binocular x <*> Binocular y = Binocular (liftA2 (<*>) x y)
instance Alternative (Binocular a b s) where
  empty = Binocular (pure empty)
  Binocular x <|> Binocular y = Binocular (liftA2 (<|>) x y)
  many = lmap repeat . manyP
  some = lmap repeat . someP
instance DisjunctiveMonoid (Binocular a b s t)
instance Filterable (Binocular a b s) where
  mapMaybe f (Binocular k) = Binocular (mapMaybe f . k)
  catMaybes (Binocular k) = Binocular (catMaybes . k)
instance Choice (Binocular a b) where
  left' (Binocular k)
    = Binocular $ fmap Left
    . k . (. (\f -> either f (const Nothing)))
  right' (Binocular k)
    = Binocular $ fmap Right
    . k . (. (\f -> either (const Nothing) f))
instance Cochoice (Binocular a b) where
  unleft (Binocular k)
    = Binocular $ catMaybes
    . fmap (either Just (const Nothing))
    . k . (. (. Left))
  unright (Binocular k)
    = Binocular $ catMaybes
    . fmap (either (const Nothing) Just)
    . k . (. (. Right))
instance CocartesianMonoidal (Binocular a b)
instance Distributor (Binocular a b)
instance CocartesianChoice (Binocular a b)
instance Alternator (Binocular a b)
instance Filtrator (Binocular a b)

{- | Run a t'Binocular' on a partial `Distributor`. -}
runBinocular
  :: (Alternator p, Filtrator p)
  => Binocular a b s t
  -> p a b -> p s t
runBinocular (Binocular k) p = k $ \f -> dimapMaybe f Just p
