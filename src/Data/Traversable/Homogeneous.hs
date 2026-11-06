{-|
Module      : Data.Traversable.Homogeneous
Description : homogeneous
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Data.Traversable.Homogeneous
  ( -- * Homogeneous
    Homogeneous (..)
    -- * Enumerable
  , Enumerable (..)
  , casesP
  , enumP
  ) where

import Control.Applicative
import Control.Lens hiding (chosen)
import Control.Lens.PartialIso
import Data.Bits ((.&.), shiftR, xor)
import Data.Complex
import Data.Functor.Compose
import qualified Data.Functor.Product as Functor
import qualified Data.Functor.Sum as Functor
import qualified Data.Monoid as Monoid
import Data.Profunctor.Monoidal
import Data.Proxy
import Data.Sequence (Seq)
import Data.Tagged
import Data.Tree (Tree (..))
import Data.Vector (Vector)
import Data.Void
import GHC.Generics

import Data.Profunctor.Distributor
import Data.Profunctor.Monoidal.Cocartesian

{- | A class of `Homogeneous`
countable sums of countable products.
-}
class Traversable t => Homogeneous t where
  {- | Sequences actions `homogeneously`.

  prop> homogeneously @Maybe = optionalP
  prop> homogeneously @[] = manyP

  Any `Traversable` & `Data.Distributive.Distributive` countable product
  can be given a default implementation for the `homogeneously` method
  with `ditraverse`.

  prop> homogeneously = ditraverse

  And any user-defined homogeneous algebraic datatype has
  a default instance for `Homogeneous`, by deriving `Generic1`.
  -}
  homogeneously :: Distributor p => p a b -> p (t a) (t b)
  default homogeneously
    :: (Generic1 t, Homogeneous (Rep1 t), Distributor p)
    => p a b -> p (t a) (t b)
  homogeneously = dimap from1 to1 . homogeneously
instance Homogeneous Par1 where
  homogeneously = dimap unPar1 Par1
instance Homogeneous Identity where
  homogeneously = dimap runIdentity Identity
instance Homogeneous Monoid.Dual where
  homogeneously = dimap Monoid.getDual Monoid.Dual
instance Homogeneous Monoid.Product where
  homogeneously = dimap Monoid.getProduct Monoid.Product
instance Homogeneous Monoid.Sum where
  homogeneously = dimap Monoid.getSum Monoid.Sum
instance Homogeneous (Tagged s) where
  homogeneously = dimap unTagged Tagged
instance Homogeneous U1 where
  homogeneously _ = pure U1
instance Homogeneous (K1 i ()) where
  homogeneously _ = pure (K1 ())
instance Homogeneous (Const ()) where
  homogeneously _ = pure (Const ())
instance Homogeneous Proxy where
  homogeneously _ = pure Proxy
instance (Homogeneous s, Homogeneous t)
  => Homogeneous (s :.: t) where
    homogeneously
      = dimap unComp1 Comp1
      . homogeneously . homogeneously
instance (Homogeneous s, Homogeneous t)
  => Homogeneous (Compose s t) where
    homogeneously
      = dimap getCompose Compose
      . homogeneously . homogeneously
instance (Homogeneous s, Homogeneous t)
  => Homogeneous (s :*: t) where
    homogeneously p = dimap2
      (\(s :*: _) -> s)
      (\(_ :*: t) -> t)
      (:*:)
      (homogeneously p)
      (homogeneously p)
instance (Homogeneous s, Homogeneous t)
  => Homogeneous (Functor.Product s t) where
    homogeneously p = dimap2
      (\(Functor.Pair s _) -> s)
      (\(Functor.Pair _ t) -> t)
      Functor.Pair
      (homogeneously p)
      (homogeneously p)
instance Homogeneous V1 where
  homogeneously _ = dimap (\case) (\case) zeroP
instance Homogeneous (K1 i Void) where
  homogeneously _ = dimap unK1 K1 zeroP
instance Homogeneous (Const Void) where
  homogeneously _ = dimap getConst Const zeroP
instance (Homogeneous s, Homogeneous t)
  => Homogeneous (s :+: t) where
    homogeneously p = dialt
      (\case {L1 s -> Left s; R1 t -> Right t})
      L1
      R1
      (homogeneously p)
      (homogeneously p)
instance (Homogeneous s, Homogeneous t)
  => Homogeneous (Functor.Sum s t) where
    homogeneously p = dialt
      (\case {Functor.InL s -> Left s; Functor.InR t -> Right t})
      Functor.InL
      Functor.InR
      (homogeneously p)
      (homogeneously p)
instance Homogeneous t
  => Homogeneous (M1 i c t) where
    homogeneously = dimap unM1 M1 . homogeneously
instance Homogeneous f => Homogeneous (Rec1 f) where
  homogeneously = dimap unRec1 Rec1 . homogeneously
instance Homogeneous Maybe where
  homogeneously = optionalP
instance Homogeneous [] where
  homogeneously = manyP
instance Homogeneous Vector where
  homogeneously p = eotList >~ p >*< homogeneously p >+< oneP
instance Homogeneous Seq where
  homogeneously p = eotList >~ p >*< homogeneously p >+< oneP
instance Homogeneous Complex where
  homogeneously p = dimap2 realPart imagPart (:+) p p
instance Homogeneous Tree where
  homogeneously p = dimap2 rootLabel subForest Node p (manyP (homogeneously p))
instance (Enum e, Bounded e) => Homogeneous ((,) e) where
  homogeneously = casesP . const

{- | A class of `Enumerable` countable sums of single values,
@t a ≅ (e, a)@ for some enumerable tag type @e@,
which is to say `Homogeneous` functors without products.

`enumerately` needs only `CocartesianMonoidal` structure,
as `Data.Profunctor.Monoidal.ditraverse` needs only
`Data.Profunctor.Monoidal.Monoidal` structure.

prop> homogeneously = enumerately

Any user-defined enumerable algebraic datatype has
a default instance for `Enumerable`, by deriving `Generic1`.
-}
class Homogeneous t => Enumerable t where
  enumerately :: CocartesianMonoidal p => p a b -> p (t a) (t b)
  default enumerately
    :: (Generic1 t, Enumerable (Rep1 t), CocartesianMonoidal p)
    => p a b -> p (t a) (t b)
  enumerately = dimap from1 to1 . enumerately
instance Enumerable Par1 where
  enumerately = dimap unPar1 Par1
instance Enumerable Identity where
  enumerately = dimap runIdentity Identity
instance Enumerable Monoid.Dual where
  enumerately = dimap Monoid.getDual Monoid.Dual
instance Enumerable Monoid.Product where
  enumerately = dimap Monoid.getProduct Monoid.Product
instance Enumerable Monoid.Sum where
  enumerately = dimap Monoid.getSum Monoid.Sum
instance Enumerable (Tagged s) where
  enumerately = dimap unTagged Tagged
instance (Enumerable s, Enumerable t)
  => Enumerable (s :.: t) where
    enumerately
      = dimap unComp1 Comp1
      . enumerately . enumerately
instance (Enumerable s, Enumerable t)
  => Enumerable (Compose s t) where
    enumerately
      = dimap getCompose Compose
      . enumerately . enumerately
instance Enumerable V1 where
  enumerately _ = dimap (\case) (\case) zeroP
instance Enumerable (K1 i Void) where
  enumerately _ = dimap unK1 K1 zeroP
instance Enumerable (Const Void) where
  enumerately _ = dimap getConst Const zeroP
instance (Enumerable s, Enumerable t)
  => Enumerable (s :+: t) where
    enumerately p = dialt
      (\case {L1 s -> Left s; R1 t -> Right t})
      L1
      R1
      (enumerately p)
      (enumerately p)
instance (Enumerable s, Enumerable t)
  => Enumerable (Functor.Sum s t) where
    enumerately p = dialt
      (\case {Functor.InL s -> Left s; Functor.InR t -> Right t})
      Functor.InL
      Functor.InR
      (enumerately p)
      (enumerately p)
instance Enumerable t
  => Enumerable (M1 i c t) where
    enumerately = dimap unM1 M1 . enumerately
instance Enumerable f => Enumerable (Rec1 f) where
  enumerately = dimap unRec1 Rec1 . enumerately
instance (Enum e, Bounded e) => Enumerable ((,) e) where
  enumerately = casesP . const

{- | `casesP` sums a `CocartesianMonoidal` over the tags
of a `Bounded` `Enum`, a dependent form of `enumerately`.
Tags are split by binary search on `fromEnum`.
`Bounded` types are inhabited, by `minBound`,
so no `zeroP` and no unreachable case is needed.

prop> enumerately = casesP . const
-}
casesP
  :: forall e p a b. (Enum e, Bounded e, CocartesianMonoidal p)
  => (e -> p a b) -> p (e, a) (e, b)
casesP p = go (fromEnum (minBound @e)) (fromEnum (maxBound @e))
  where
    go :: Int -> Int -> p (e, a) (e, b)
    go lo hi
      | lo >= hi = dimap snd (toEnum lo,) (p (toEnum lo))
      | otherwise = dialt
          (\ea@(e, _) -> if fromEnum e <= mid then Left ea else Right ea)
          id
          id
          (go lo mid)
          (go (mid + 1) hi)
      where
        -- floor average without overflow, Hacker's Delight §2-5
        mid = (lo .&. hi) + ((lo `xor` hi) `shiftR` 1)

{- | `enumP` sums a `CocartesianMonoidal` of nullary patterns
over the values of a `Bounded` `Enum`.

prop> enumP p = dimap (,()) fst (casesP p)
-}
enumP
  :: (Enum e, Bounded e, CocartesianMonoidal p)
  => (e -> p () ()) -> p e e
enumP p = dimap (,()) fst (casesP p)
