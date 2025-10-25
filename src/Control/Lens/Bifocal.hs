{- |
Module      : Control.Lens.Bifocal
Description : bifocals
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Control.Lens.Bifocal
  ( -- * Bifocal
    Bifocal
  , ABifocal
    -- * Combinators
  , bifocal
  , mapBifocal
  , cloneBifocal
  , withBifocal
  , chained1
  , chained
    -- * Binocular
  , Binocular (..), runBinocular
    -- * Prismoid
  , Prismoid
  , somed
  , lefted
  , righted
    -- * Filtroid
  , Filtroid
  , unlefted
  , unrighted
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.Grammar.Equator
import Control.Lens.Internal.Profunctor
import Control.Lens.PartialIso
import Control.Lens.Grammar.Stream
import Data.Profunctor
import Data.Profunctor.Distributor
import Witherable

{- | `Bifocal`s are bidirectional parser optics.

Every one of the following is a `Bifocal`.

* `Control.Lens.Iso.Iso`
* `Control.Lens.Prism.Prism`
* `Control.Lens.Monocle.Monocle`
* `Control.Lens.Diopter.Diopter`
* `Prismoid` & `Filtroid`

`Bifocal`s are isomorphic to `Binocular`s.
-}
type Bifocal s t a b = forall p f.
  (Alternator p, Filtrator p, Alternative f, Filterable f)
    => p a (f b) -> p s (f t)

{- | If you see `ABifocal` in a signature for a function,
the function is expecting a `Bifocal`. -}
type ABifocal s t a b =
  Binocular a b a (Maybe b) -> Binocular a b s (Maybe t)

{- | `Prismoid`s generalize `Bifocal`s, combining
`Control.Lens.Prism.Prism`s and `Control.Lens.Diopter.Diopter`s. -}
type Prismoid s t a b = forall p f.
  (Alternator p, Alternative f)
    => p a (f b) -> p s (f t)

{- | An optic for `Filtrator`s, `Filtroid`s generalize `Bifocal`s. -}
type Filtroid s t a b = forall p f.
  (Filtrator p, Filterable f)
    => p a (f b) -> p s (f t)

{- | Build a `Bifocal` from a concrete `Binocular`. -}
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

{- | One or more. -}
somed :: Prismoid [a] [b] a b
somed = unwrapPafb . someP . WrapPafb

{- | `lefted` is like `_Left`, except
with heterogeneous `Right` parameters. -}
lefted :: Prismoid (Either a c) (Either b d) a b
lefted = unwrapPafb . alternate . Left . WrapPafb


{- | `righted` is like `_Right`, except
with heterogeneous `Left` parameters. -}
righted :: Prismoid (Either c a) (Either d b) a b
righted = unwrapPafb . alternate . Right . WrapPafb

{- | Dual to `lefted`. -}
unlefted :: Filtroid a b (Either a c) (Either b d)
unlefted = unwrapPafb . fst . filtrate . WrapPafb

{- | Dual to `righted`. -}
unrighted :: Filtroid a b (Either c a) (Either d b)
unrighted = unwrapPafb . snd . filtrate . WrapPafb

{- |
Associate a binary constructor pattern to sequence one or more times.
-}
chained1 :: (forall x. x -> Either x x) -> APartialIso a b (a,a) (b,b) -> Bifocal a b a b
chained1 assoc binPat = unwrapPafb . chain1 assoc binPat noSep . WrapPafb

{- |
Associate a binary constructor pattern to sequence one or more times,
or use a nilary constructor pattern to sequence zero times.
-}
chained :: (forall x. x -> Either x x) -> APartialIso a b (a,a) (b,b) -> APartialIso a b () () -> Bifocal a b a b
chained assoc binPat nilPat = unwrapPafb . chain assoc binPat nilPat noSep . WrapPafb

{- | Run `ABifocal` over an `Alternative` & `Filterable`. -}
withBifocal
  :: (Alternative f, Filterable f)
  => ABifocal s t a b -> ((s -> Maybe a) -> f b) -> f t
withBifocal bif = unBinocular (catMaybes (bif (Just <$> equate)))

{- | `Binocular` provides an efficient
concrete representation of `Bifocal`s. -}
newtype Binocular a b s t = Binocular
  { unBinocular
      :: forall f. (Alternative f, Filterable f)
      => ((s -> Maybe a) -> f b) -> f t
  }
instance Equator a b (Binocular a b) where
  equate = Binocular ($ Just)
instance Profunctor (Binocular a b) where
  dimap f g (Binocular k) = Binocular $ fmap g . k . (. (. f))
instance Functor (Binocular a b s) where fmap = rmap
instance Applicative (Binocular a b s) where
  pure t = Binocular (pure (pure t))
  Binocular x <*> Binocular y = Binocular (liftA2 (<*>) x y)
instance Alternative (Binocular a b s) where
  empty = Binocular (pure empty)
  Binocular x <|> Binocular y = Binocular (liftA2 (<|>) x y)
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
instance Distributor (Binocular a b)
instance Alternator (Binocular a b)
instance Filtrator (Binocular a b)

{- | Run a `Binocular` on a partial `Distributor`. -}
runBinocular
  :: (Alternator p, Filtrator p)
  => Binocular a b s t
  -> p a b -> p s t
runBinocular (Binocular k) p = k $ \f -> dimapMaybe f Just p
