{- |
Module      : Control.Lens.Grate
Description : grates
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable

See [Grate: A new kind of Optic](https://r6research.livejournal.com/28050.html)
-}

module Control.Lens.Grate
  ( Grate
  , Grate'
  , AGrate
  , AGrate'
  , grate
  , cotraversed
  , represented
  , mapGrate
  , cloneGrate
  , withGrate
  , distributing
  , cotraverseOf
  , distributeOf
  , collectOf
  , Grating (..)
  ) where

import Data.Distributive
import Data.Function
import Data.Functor.Identity
import Data.Functor.Rep
import Data.Profunctor
import Data.Profunctor.Distributor

type Grate s t a b = forall p f.
  (Closed p, Monoidal p, Distributive f, Applicative f)
    => p a (f b) -> p s (f t)

type Grate' s a = Grate s s a a

type AGrate s t a b =
  Grating a b a (Identity b) -> Grating a b s (Identity t)

type AGrate' s a = AGrate s s a a

grate :: (((s -> a) -> b) -> t) -> Grate s t a b
grate f = dimap (&) (cotraverse f) . closed

cotraversed :: Distributive g => Grate (g a) (g b) a b
cotraversed = grate $ flip cotraverse id

represented :: Representable g => Grate (g a) (g b) a b
represented = grate $ tabulate . (. flip index)

mapGrate :: Closed p => AGrate s t a b -> p a b -> p s t
mapGrate grt = dimap (&) (withGrate grt) . closed

cloneGrate :: AGrate s t a b -> Grate s t a b
cloneGrate = grate . withGrate

withGrate :: AGrate s t a b -> ((s -> a) -> b) -> t
withGrate grt = runGrating $ runIdentity <$> grt (Identity <$> anyToken)

distributing
  :: (Closed p, forall x. Functor (p x), Distributive g)
  => AGrate s t a b -> p a (g b) -> g (p s t)
distributing grt
  = distribute
  . dimap (&) (cotraverse (withGrate grt))
  . closed

cotraverseOf :: Functor f => AGrate s t a b -> (f a -> b) -> f s -> t
cotraverseOf grt = runCostar . mapGrate grt . Costar

distributeOf :: Functor f => AGrate s t b (f b) -> f s -> t
distributeOf grt = cotraverseOf grt id

collectOf :: Functor f => AGrate s t b (f b) -> (a -> s) -> f a -> t
collectOf grt f = distributeOf grt . fmap f

newtype Grating a b s t = Grating
  {runGrating :: ((s -> a) -> b) -> t}
instance Functor (Grating a b s) where fmap = fmapRep
instance Applicative (Grating a b s) where
  pure = pureRep
  (<*>) = apRep
instance Tokenized a b (Grating a b) where
  anyToken = Grating ($ id)
instance Distributive (Grating a b s) where
  distribute = distributeRep
  collect = collectRep
instance Representable (Grating a b s) where
  type Rep (Grating a b s) = (s -> a) -> b
  index (Grating k) f = k f
  tabulate = Grating
