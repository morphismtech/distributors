{- |
Module      :  Control.Lens.Bifocal
Description :  monocles
Copyright   :  (C) 2024 - Eitan Chatav
License     :  BSD-style (see the file LICENSE)
Maintainer  :  Eitan Chatav <eitan.chatav@gmail.com>
Stability   :  provisional
Portability :  non-portable

A `Bifocal`s is an isomorphism to
one of a fixed list of fixed lengths of tuples.
-}
module Control.Lens.Bifocal2
  ( Bifocal
  , Bifocal'
  , ABifocal
  , ABifocal'
  , withBifocal
  , bicycle
  , Pafb (..)
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.Internal.FunList
import Data.Distributive
import Data.Functor.Compose
import Data.Profunctor
import Data.Profunctor.Distributor
import Data.Profunctor.Monoidal
import Witherable

type Bifocal s t a b = forall p f.
  ( Choice p
  , Cochoice p
  , Distributor p
  , forall x. (Filterable (p x))
  , forall x. (Alternative (p x))
  , Filterable f
  , Alternative f
  ) => p a (f b) -> p s (f t)

type Bifocal' s a = Bifocal s s a a

type ABifocal s t a b =
  Posh a b a (Maybe b) -> Posh a b s (Maybe t)

type ABifocal' s a = ABifocal s s a a

withBifocal :: ABifocal s t a b -> (Posh a b s t -> r) -> r
withBifocal bif k = k (catMaybes (bif (Just <$> posh)))

bicycle
  :: ( Choice p
     , Cochoice p
     , forall x. Filterable (p x)
     , forall x. Alternative (p x)
     )
  => ABifocal s t a b -> p a b -> p s t
bicycle bif p =
  withBifocal bif $ \po ->
    runPosh po $ \_ -> p

newtype Pafb f p a b = Pafb {runPafb :: p a (f b)}
instance
  ( Functor f
  , Profunctor p
  ) => Functor (Pafb f p a) where fmap = rmap
instance
  ( Functor f
  , Profunctor p
  ) => Profunctor (Pafb f p) where
    dimap f g (Pafb p) = Pafb (dimap f (fmap g) p)
deriving via (Compose (p a) f) instance
  ( Applicative f
  , forall x. Applicative (p x)
  , Profunctor p
  ) => Applicative (Pafb f p a)
instance
  ( Applicative f
  , forall x. Applicative (p x)
  , Profunctor p
  ) => Monoidal (Pafb f p)
instance
  ( Filterable f
  , Profunctor p
  ) => Filterable (Pafb f p a) where
    catMaybes (Pafb p) = Pafb (rmap catMaybes p)
    mapMaybe f (Pafb p) = Pafb (rmap (mapMaybe f) p)
instance
  ( Filterable f
  , Profunctor p
  ) => Cochoice (Pafb f p) where
    unleft (Pafb p) = Pafb $
      dimap Left (mapMaybe (either Just (const Nothing))) p
    unright (Pafb p) = Pafb $
      dimap Right (mapMaybe (either (const Nothing) Just)) p
instance
  ( Applicative f
  , Choice p
  ) => Choice (Pafb f p) where
  left' (Pafb p) = Pafb $
    rmap (either (fmap Left) (pure . Right)) (left' p)
deriving via (Compose (p a) f) instance
  ( Applicative f
  , forall x. Alternative (p x)
  , Profunctor p
  ) => Alternative (Pafb f p a)
instance
  ( Applicative f
  , Filterable f
  , forall x. (Alternative (p x))
  , Choice p
  ) => Distributor (Pafb f p)
instance
  ( Distributive f
  , Closed p
  ) => Closed (Pafb f p) where
    closed (Pafb p) = Pafb (rmap distribute (closed p))
