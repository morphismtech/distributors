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
  ) where

import Control.Applicative
import Control.Lens.Internal.FunList
import Data.Profunctor
import Data.Profunctor.Distributor
import Witherable

type Bifocal s t a b = forall p f.
  ( Choice p
  , Cochoice p
  , Distributor p
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
