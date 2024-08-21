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
module Control.Lens.Bifocal
  ( Bifocal
  , bifocal0
  , bifocal2
  , BifocalNs (..)
  , _Flag
  , _Sign
  , _Option
  , _Many
  , _Many1
  , _Sep
  , _Sep1
  , _Some
  , _SepSome
  ) where

import Control.Lens
import Control.Lens.Internal.FunList
import Control.Lens.Internal.Profunctor
import Control.Lens.Monocle
import Control.Lens.Stream
import Data.Profunctor.Distributor
import Data.Void

type Bifocal s t a b = forall p f.
  (Distributor p, Applicative f)
    => p a (f b) -> p s (f t)

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
_Sign :: Bifocal (Ordering, a) (Ordering, b) a b
_Sign p = iso hither thither
  (dialt id (fmap Left) (fmap Right) p (bifocal2 p)) where
    hither (LT, a) = Left a
    hither (EQ, a) = Right (Left a)
    hither (GT, a) = Right (Right a)
    thither (Left a) = (LT, a)
    thither (Right (Left a)) = (EQ, a)
    thither (Right (Right a)) = (GT, a)
_Option :: Bifocal (Maybe a) (Maybe b) a b
_Option
  = unwrapPafb
  . optionP
  . WrapPafb
_Many :: Stream s t a b => Bifocal s t a b
_Many
  = unwrapPafb
  . manyP
  . WrapPafb
_Many1 :: Stream s t a b => Bifocal (a,s) (b,t) a b
_Many1
  = unwrapPafb
  . many1
  . WrapPafb
_Sep
  :: (Stream s t a b, Distributor p, Applicative f)
  => Sep p -> Optic p f s t a b
_Sep Sep {by = comma, beginBy = beg, endBy = end}
  = unwrapPafb
  . atLeast0 Sep
    { by = WrapPafb (rmap pure comma)
    , beginBy = WrapPafb (rmap pure beg)
    , endBy = WrapPafb (rmap pure end)
    }
  . WrapPafb
_Sep1
  :: (Stream s t a b, Choice p, Distributor p, Applicative f)
  => Sep p -> Optic p f (a,s) (b,t) a b
_Sep1 Sep {by = comma, beginBy = beg, endBy = end}
  = unwrapPafb
  . moreThan0 Sep
    { by = WrapPafb (rmap pure comma)
    , beginBy = WrapPafb (rmap pure beg)
    , endBy = WrapPafb (rmap pure end)
    }
  . WrapPafb

_Some
  :: ( Choice p
     , Distributor p
     , Applicative f
     , Stream s t a b
     , Cons s t a b
     ) => Optic p f s t a b
_Some = _Cons . _Many1
_SepSome
  :: ( Choice p
     , Distributor p
     , Applicative f
     , Stream s t a b
     , Cons s t a b
     )
  => Sep p -> Optic p f s t a b
_SepSome s = _Cons . _Sep1 s

data SomeV (ns :: [Peano]) x where
  Fst :: V n x -> SomeV (n ': ns) x
  Nxt :: SomeV ns x -> SomeV (n ': ns) x
eSomeV :: SomeV (n ': ns) x -> Either (V n x) (SomeV ns x)
eSomeV = \case
  Fst v -> Left v
  Nxt sv -> Right sv

class BifocalNs (ns :: [Peano]) where
  bifocalV :: Bifocal (SomeV ns a) (SomeV ns b) a b
instance BifocalNs '[] where
  bifocalV _ = emptyP (\case)
instance (MonocleN n, BifocalNs ns) =>
  BifocalNs (n ': ns) where
    bifocalV p = dialt
      eSomeV
      (fmap Fst)
      (fmap Nxt)
      (monocleV @n p)
      (bifocalV @ns p)
