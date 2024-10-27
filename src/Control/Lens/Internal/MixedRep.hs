module Control.Lens.Internal.MixedRep where

import Control.Applicative
import Data.Profunctor
import Data.Distributive
import Data.Functor.Apply
import Data.Functor.Compose
import Witherable

newtype MixedRep f p a b = MixedRep {runMixedRep :: p a (f b)}
instance
  ( Functor f
  , Profunctor p
  ) => Functor (MixedRep f p a) where fmap = rmap
instance
  ( Functor f
  , Profunctor p
  ) => Profunctor (MixedRep f p) where
    dimap f g (MixedRep p) = MixedRep (dimap f (fmap g) p)
deriving via (Compose (p a) f) instance
  ( Apply f
  , forall x. Apply (p x)
  , Profunctor p
  ) => Apply (MixedRep f p a)
deriving via (Compose (p a) f) instance
  ( Applicative f
  , forall x. Applicative (p x)
  , Profunctor p
  ) => Applicative (MixedRep f p a)
instance
  ( Filterable f
  , Profunctor p
  ) => Filterable (MixedRep f p a) where
    catMaybes (MixedRep p) = MixedRep (rmap catMaybes p)
    mapMaybe f (MixedRep p) = MixedRep (rmap (mapMaybe f) p)
instance
  ( Filterable f
  , Profunctor p
  ) => Cochoice (MixedRep f p) where
    unleft (MixedRep p) = MixedRep $
      dimap Left (mapMaybe (either Just (const Nothing))) p
    unright (MixedRep p) = MixedRep $
      dimap Right (mapMaybe (either (const Nothing) Just)) p
instance
  ( Applicative f
  , Choice p
  ) => Choice (MixedRep f p) where
    left' (MixedRep p) = MixedRep $
      rmap (either (fmap Left) (pure . Right)) (left' p)
    right' (MixedRep p) = MixedRep $
      rmap (either (pure . Left) (fmap Right)) (right' p)
deriving via (Compose (p a) f) instance
  ( Applicative f
  , forall x. Alternative (p x)
  , Profunctor p
  ) => Alternative (MixedRep f p a)
instance
  ( Distributive f
  , Closed p
  ) => Closed (MixedRep f p) where
    closed (MixedRep p) = MixedRep (rmap distribute (closed p))
