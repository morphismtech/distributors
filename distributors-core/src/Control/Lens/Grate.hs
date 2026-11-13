{- |
Module      : Control.Lens.Grate
Description : grates
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable

See O'Connor, [Grate: A new kind of Optic]
(https://r6research.livejournal.com/28050.html)
-}

module Control.Lens.Grate
  ( -- * Grate
    Grate
  , AGrate
  , Grating (..)
  , Diffraction (..), diffraction, withDiffraction
    -- * Combinators
  , grate
  , withGrate
  , cloneGrate
  , mapGrate
  , cotraversed
  , represented
  , cotraverseOf
  , distributeOf
  , collectOf
  , distributing
  ) where

import Data.Distributive
import Data.Function
import Data.Functor.Identity
import Data.Functor.Rep
import Data.Profunctor
import Data.Profunctor.Monoidal

-- $setup
-- >>> import Control.Lens (over)
-- >>> import Data.Complex

{- | `Grate`s are an optic that are dual to
`Control.Lens.Traversal.Traversal`s, as `Distributive` is `Traversable`.

`Control.Lens.Iso.Iso` ⊂ `Control.Lens.Monocle.Monocle` ⊂ `Grate`.

`Grate`s are isomorphic to t'Grating's, & to t'Diffraction's,
whose shapes are `Distributive`.
-}
type Grate s t a b = forall p f.
  (Closed p, Monoidal p, Distributive f, Applicative f)
    => p a (f b) -> p s (f t)

{- | `AGrate` is monomorphically a `Grate`.

> prop> Grate s t a b ⊂ AGrate s t a b
-}
type AGrate s t a b =
  Grating a b a (Identity b) -> Grating a b s (Identity t)

{- | Build a `Grate`. -}
grate :: (((s -> a) -> b) -> t) -> Grate s t a b
grate f = dimap (&) (cotraverse f) . closed

{- | Build a `Grate` from a `Distributive`. -}
cotraversed :: Distributive g => Grate (g a) (g b) a b
cotraversed = grate $ flip cotraverse id

{- | Build a `Grate` from a `Representable`. -}
represented :: Representable g => Grate (g a) (g b) a b
represented = grate $ tabulate . (. flip index)

{- | Action of `AGrate` on `Closed` `Profunctor`s. -}
mapGrate :: Closed p => AGrate s t a b -> p a b -> p s t
mapGrate grt = dimap (&) (withGrate grt) . closed

{- | Clone `AGrate` so that you can reuse the same
monomorphically typed `Grate` for different purposes.
-}
cloneGrate :: AGrate s t a b -> Grate s t a b
cloneGrate = grate . withGrate

{- | Run `AGrate`. -}
withGrate :: AGrate s t a b -> ((s -> a) -> b) -> t
withGrate grt = runGrating $ runIdentity <$> grt (Identity <$> Grating ($ id))

{- | Distribute over a `Closed` `Profunctor`. -}
distributing
  :: (Closed p, forall x. Functor (p x), Distributive g)
  => AGrate s t a b -> p a (g b) -> g (p s t)
distributing grt
  = distribute
  . dimap (&) (cotraverse (withGrate grt))
  . closed

{- | Dual to `Control.Lens.Combinators.traverseOf`. -}
cotraverseOf :: Functor f => AGrate s t a b -> (f a -> b) -> f s -> t
cotraverseOf grt = runCostar . mapGrate grt . Costar

{- | Dual to `Control.Lens.Combinators.sequenceAOf`. -}
distributeOf :: Functor f => AGrate s t b (f b) -> f s -> t
distributeOf grt = cotraverseOf grt id

{- | `collect` with `AGrate`. -}
collectOf :: Functor f => AGrate s t b (f b) -> (a -> s) -> f a -> t
collectOf grt f = distributeOf grt . fmap f

{- | t'Grating' provides an efficient
concrete representation of `Grate`s. -}
newtype Grating a b s t = Grating
  {runGrating :: ((s -> a) -> b) -> t}
instance Profunctor (Grating a b) where
  dimap f g (Grating k) = Grating (g . k . (. (. f)))
instance Closed (Grating a b) where
  closed (Grating k) = Grating $ \f x -> k $ \g -> f (g . ($ x))
instance Functor (Grating a b s) where fmap = fmapRep
instance Applicative (Grating a b s) where
  pure = pureRep
  (<*>) = apRep
instance Distributive (Grating a b s) where
  distribute = distributeRep
  collect = collectRep
instance Representable (Grating a b s) where
  type Rep (Grating a b s) = (s -> a) -> b
  index (Grating k) f = k f
  tabulate = Grating

{- | t'Diffraction' is a secondary concrete representation of `Grate`s,
by `Distributive` shapes, into which a source splits its foci,
& from which a target merges them, as
t'Control.Lens.Monocle.Ditraversal's are of
`Control.Lens.Monocle.Monocle`s, by `Traversable` & `Distributive` shapes.

>>> over (diffraction (Diffraction (uncurry (:+)) (\(x :+ y) -> (x, y)))) negate (1, 2)
(-1,-2)
-}
data Diffraction a b s t where
  Diffraction
    :: Distributive f
    => (s -> f a) -> (f b -> t) -> Diffraction a b s t
instance Profunctor (Diffraction a b) where
  dimap f g (Diffraction split merge) = Diffraction (split . f) (g . merge)
instance Functor (Diffraction a b s) where fmap = rmap

{- | Build a `Grate` from a t'Diffraction',
getting each focus of its shape by `distribute`.
-}
diffraction :: Diffraction a b s t -> Grate s t a b
diffraction (Diffraction split merge) =
  grate $ \get -> merge (fmap get (distribute split))

{- | Convert `AGrate` to the pair of functions that characterize it,
splitting into & merging from a `Distributive` shape,
the functions of getters, as a t'Grating' is.

>>> withDiffraction cotraversed $ \split merge -> merge (fmap (+ 1) (split (1 :+ 2))) :: Complex Int
2 :+ 3
-}
withDiffraction
  :: AGrate s t a b
  -> (forall f. Distributive f => (s -> f a) -> (f b -> t) -> r)
  -> r
withDiffraction grt k = k (\s get -> get s) (withGrate grt)
