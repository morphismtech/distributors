{- |
Module      : Control.Lens.Grate
Description : grates
Copyright   : (C) 2025 - Eitan Chatav
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
    -- * Grating
  , Grating (..)
  ) where

import Control.Lens.Grammar.Equator
import Data.Distributive
import Data.Function
import Data.Functor.Identity
import Data.Functor.Rep
import Data.Profunctor
import Data.Profunctor.Monoidal

{- | `Grate`s are an optic that are dual to
`Control.Lens.Traversal.Traversal`s, as `Distributive` is `Traversable`.

Every `Control.Lens.Monocle.Monocle` is a `Grate`.

`Grate`s are isomorphic to `Grating`s.
-}
type Grate s t a b = forall p f.
  (Closed p, Monoidal p, Distributive f, Applicative f)
    => p a (f b) -> p s (f t)

{- | If you see `AGrate` in a signature for a function,
the function is expecting a `Grate`. -}
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
withGrate grt = runGrating $ runIdentity <$> grt (Identity <$> equate)

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

{- | `Grating` provides an efficient
concrete representation of `Grate`s. -}
newtype Grating a b s t = Grating
  {runGrating :: ((s -> a) -> b) -> t}
instance Functor (Grating a b s) where fmap = fmapRep
instance Applicative (Grating a b s) where
  pure = pureRep
  (<*>) = apRep
instance Equator a b (Grating a b) where
  equate = Grating ($ id)
instance Distributive (Grating a b s) where
  distribute = distributeRep
  collect = collectRep
instance Representable (Grating a b s) where
  type Rep (Grating a b s) = (s -> a) -> b
  index (Grating k) f = k f
  tabulate = Grating
