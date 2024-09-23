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

{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}

module Control.Lens.Bifocal
  ( Bifocal
  , Bifocal'
  , ABifocal
  , ABifocal'
  , withBifocal
  , cloneBifocal
  , bifocal0
  , bifocal2
  , BifocalNs (..)
  , _Flag
  , _FlagSign
  , _Option
  , _Many
  , _Many1
  , _Sep
  , _Sep1
  , _Some
  , _SepSome
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.Internal.FunList
import Control.Lens.Monocle
import Control.Lens.Stream
import Data.Profunctor
import Data.Profunctor.Distributor
import Data.Void
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

cloneBifocal :: ABifocal s t a b -> Bifocal s t a b
cloneBifocal bif = runPafb . bicycle bif . Pafb

bifocal0 :: Bifocal Void t a b
bifocal0 _ = emptyP absurd

bifocal2 :: Bifocal (Either a a) (Either b b) a b
bifocal2 p = dialt id (fmap Left) (fmap Right) p p

_Flag :: Bifocal (Bool, a) (Bool, b) a b
_Flag = iso hither thither . bifocal2 where
  hither (False, a) = Left a
  hither (True, a) = Right a
  thither (Left a) = (False, a)
  thither (Right a) = (True, a)

_FlagSign :: Bifocal (Ordering, a) (Ordering, b) a b
_FlagSign p = iso hither thither
  (dialt id (fmap Left) (fmap Right) p (bifocal2 p)) where
    hither (LT, a) = Left a
    hither (EQ, a) = Right (Left a)
    hither (GT, a) = Right (Right a)
    thither (Left a) = (LT, a)
    thither (Right (Left a)) = (EQ, a)
    thither (Right (Right a)) = (GT, a)

_Option :: Bifocal (Maybe a) (Maybe b) a b
_Option = runPafb . optionP . Pafb

_Many :: Stream s t a b => Bifocal s t a b
_Many = runPafb . manyP . Pafb

_Many1 :: Stream s t a b => Bifocal (a,s) (b,t) a b
_Many1 = runPafb . many1 . Pafb

_Some :: (Stream s t a b, Cons s t a b) => Bifocal s t a b
_Some = _Cons . _Many1

type Byfocal s t a b = forall p f.
  ( Choice p
  , Cochoice p
  , Distributor p
  , forall x. (Filterable (p x))
  , forall x. (Alternative (p x))
  , Filterable f
  , Alternative f
  ) => By p -> p a (f b) -> p s (f t)

_Sep :: Stream s t a b => Byfocal s t a b
_Sep By {separator = comma, beginBy = beg, endBy = end}
  = runPafb
  . sep By
    { separator = Pafb (rmap pure comma)
    , beginBy = Pafb (rmap pure beg)
    , endBy = Pafb (rmap pure end)
    }
  . Pafb

_Sep1 :: Stream s t a b => Byfocal (a,s) (b,t) a b
_Sep1 By {separator = comma, beginBy = beg, endBy = end}
  = runPafb
  . sep1 By
    { separator = Pafb (rmap pure comma)
    , beginBy = Pafb (rmap pure beg)
    , endBy = Pafb (rmap pure end)
    }
  . Pafb

_SepSome :: (Stream s t a b, Cons s t a b) => Byfocal s t a b
_SepSome s = _Cons . _Sep1 s

class BifocalNs (ns :: [Peano]) where
  bifocalV :: Bifocal (SomeV ns a) (SomeV ns b) a b
instance BifocalNs '[] where
  bifocalV _ = emptyP (\case)
instance (MonocleN n, BifocalNs ns) =>
  BifocalNs (n ': ns) where
    bifocalV p = dialt
      (\case
        VFst v -> Left v
        VNxt sv -> Right sv)
      (fmap VFst)
      (fmap VNxt)
      (monocleV @n p)
      (bifocalV @ns p)
