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
  ) where

import Control.Applicative
import Control.Lens hiding (chosen)
import Control.Lens.PartialIso
import Control.Monad.Trans.Identity (IdentityT (..))
import Data.Complex
import Data.Functor.Compose
import qualified Data.Functor.Product as Functor
import qualified Data.Functor.Sum as Functor
import qualified Data.Monoid as Monoid
import Data.Ord (Down (..))
import qualified Data.Semigroup as Semigroup
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
instance Homogeneous Down where
  homogeneously = dimap getDown Down
instance Homogeneous Semigroup.Min where
  homogeneously = dimap Semigroup.getMin Semigroup.Min
instance Homogeneous Semigroup.Max where
  homogeneously = dimap Semigroup.getMax Semigroup.Max
instance Homogeneous Semigroup.First where
  homogeneously = dimap Semigroup.getFirst Semigroup.First
instance Homogeneous Semigroup.Last where
  homogeneously = dimap Semigroup.getLast Semigroup.Last
instance Homogeneous f => Homogeneous (Monoid.Alt f) where
  homogeneously = dimap Monoid.getAlt Monoid.Alt . homogeneously
instance Homogeneous f => Homogeneous (Monoid.Ap f) where
  homogeneously = dimap Monoid.getAp Monoid.Ap . homogeneously
instance Homogeneous f => Homogeneous (IdentityT f) where
  homogeneously = dimap runIdentityT IdentityT . homogeneously
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

{- | A class of `Enumerable` countable sums of single copies,
which are `Homogeneous`, & sequenced by sums alone.

prop> enumerably @Identity = dimap runIdentity Identity

Every `Enumerable` is sequenced `enumerably` as it's sequenced
`homogeneously`, by a `Distributor`.

prop> enumerably = homogeneously

And any user-defined enumerable algebraic datatype has
a default instance for `Enumerable`, by deriving `Generic1`.
-}
class Homogeneous f => Enumerable f where
  {- | Sequences an action on the copy which a sum holds. -}
  enumerably :: CocartesianMonoidal p => p a b -> p (f a) (f b)
  default enumerably
    :: (Generic1 f, Enumerable (Rep1 f), CocartesianMonoidal p)
    => p a b -> p (f a) (f b)
  enumerably = dimap from1 to1 . enumerably
instance Enumerable Par1 where
  enumerably = dimap unPar1 Par1
instance Enumerable Identity where
  enumerably = dimap runIdentity Identity
instance Enumerable Monoid.Dual where
  enumerably = dimap Monoid.getDual Monoid.Dual
instance Enumerable Monoid.Product where
  enumerably = dimap Monoid.getProduct Monoid.Product
instance Enumerable Monoid.Sum where
  enumerably = dimap Monoid.getSum Monoid.Sum
instance Enumerable (Tagged s) where
  enumerably = dimap unTagged Tagged
instance Enumerable Down where
  enumerably = dimap getDown Down
instance Enumerable Semigroup.Min where
  enumerably = dimap Semigroup.getMin Semigroup.Min
instance Enumerable Semigroup.Max where
  enumerably = dimap Semigroup.getMax Semigroup.Max
instance Enumerable Semigroup.First where
  enumerably = dimap Semigroup.getFirst Semigroup.First
instance Enumerable Semigroup.Last where
  enumerably = dimap Semigroup.getLast Semigroup.Last
instance Enumerable f => Enumerable (Monoid.Alt f) where
  enumerably = dimap Monoid.getAlt Monoid.Alt . enumerably
instance Enumerable f => Enumerable (Monoid.Ap f) where
  enumerably = dimap Monoid.getAp Monoid.Ap . enumerably
instance Enumerable f => Enumerable (IdentityT f) where
  enumerably = dimap runIdentityT IdentityT . enumerably
instance (Enumerable s, Enumerable t)
  => Enumerable (s :.: t) where
    enumerably = dimap unComp1 Comp1 . enumerably . enumerably
instance (Enumerable s, Enumerable t)
  => Enumerable (Compose s t) where
    enumerably = dimap getCompose Compose . enumerably . enumerably
instance Enumerable V1 where
  enumerably _ = dimap (\case) (\case) zeroP
instance Enumerable (K1 i Void) where
  enumerably _ = dimap unK1 K1 zeroP
instance Enumerable (Const Void) where
  enumerably _ = dimap getConst Const zeroP
instance (Enumerable s, Enumerable t)
  => Enumerable (s :+: t) where
    enumerably p = dialt
      (\case {L1 s -> Left s; R1 t -> Right t})
      L1
      R1
      (enumerably p)
      (enumerably p)
instance (Enumerable s, Enumerable t)
  => Enumerable (Functor.Sum s t) where
    enumerably p = dialt
      (\case {Functor.InL s -> Left s; Functor.InR t -> Right t})
      Functor.InL
      Functor.InR
      (enumerably p)
      (enumerably p)
instance Enumerable t => Enumerable (M1 i c t) where
  enumerably = dimap unM1 M1 . enumerably
instance Enumerable f => Enumerable (Rec1 f) where
  enumerably = dimap unRec1 Rec1 . enumerably
