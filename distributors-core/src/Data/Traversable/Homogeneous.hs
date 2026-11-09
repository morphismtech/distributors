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
  , zipHomogeneous
  , zipWithHomogeneous
  , zipWithHomogeneous3
  , zipWithHomogeneousM
  , transposeHomogeneous
    -- * Zipporah
  , Zipporah (..)
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
import Data.Monoid.Disjunctive
import Data.Profunctor (Cochoice (..), Star (..))
import Data.Profunctor.Monoidal
import Data.Proxy
import Data.Sequence (Seq)
import Data.Tagged
import Data.Tree (Tree (..))
import Data.Vector (Vector)
import Data.Void
import GHC.Generics
import Witherable (Filterable (..))

import Data.Profunctor.Distributor
import Data.Profunctor.Monadic (Monadic)
import Data.Profunctor.Monoidal.Cocartesian

{- | A class of `Homogeneous`
countable sums of countable products.
-}
class Traversable t => Homogeneous t where
  {- | Sequences actions `homogeneously`.

  > prop> homogeneously @Maybe = optionalP
  > prop> homogeneously @[] = manyP

  Any `Traversable` & `Data.Distributive.Distributive` countable product
  can be given a default implementation for the `homogeneously` method
  with `ditraverse`.

  > prop> homogeneously = ditraverse

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
  homogeneously p = eotList . swapped >~ p >*< homogeneously p >+< oneP
instance Homogeneous Seq where
  homogeneously p = eotList . swapped >~ p >*< homogeneously p >+< oneP
instance Homogeneous Complex where
  homogeneously p = dimap2 realPart imagPart (:+) p p
instance Homogeneous Tree where
  homogeneously p = dimap2 rootLabel subForest Node p (manyP (homogeneously p))

{- | A copy tagged by a finite enumeration is a copy for each tag,
summed in a balanced tree, built lazily.

>>> zipWithHomogeneous (+) (True, 1) (True, 2 :: Int)
Just (True,3)
>>> zipWithHomogeneous (+) (True, 1) (False, 2 :: Int)
Nothing
-}
instance (Enum e, Bounded e) => Homogeneous ((,) e) where
  homogeneously p = go (tag (minBound :: e)) (tag (maxBound :: e))
    where
      tag = toInteger . fromEnum
      go lo hi
        | lo >= hi = dimap snd (toEnum (fromInteger lo),) p
        | otherwise = dialt
            (\ea -> if tag (fst ea) <= mid then Left ea else Right ea)
            id id (go lo mid) (go (mid + 1) hi)
        where
          mid = (lo + hi) `div` 2

{- | Zip `Homogeneous` structures in the positions of a `Traversable`,
by a function of their elements at each position, when they have the
same shape, or else `empty`.

>>> zipHomogeneous (Just . sum) [[1, 2], [3, 4], [5, 6 :: Int]]
Just [9,12]
>>> zipHomogeneous (Just . sum) [[1, 2], [3 :: Int]]
Nothing
>>> zipHomogeneous id [[1, 2], [3, 4 :: Int]]
[[1,2],[1,4],[3,2],[3,4]]
-}
zipHomogeneous
  :: (Homogeneous t, Traversable f, Alternative g)
  => (f a -> g b) -> f (t a) -> g (t b)
zipHomogeneous f = runZipporah (homogeneously (Zipporah f))

{- | Zip two `Homogeneous` structures, when they have the same shape.

>>> zipWithHomogeneous (+) [1, 2] [3, 4 :: Int]
Just [4,6]
>>> zipWithHomogeneous (+) [1] [3, 4 :: Int]
Nothing
-}
zipWithHomogeneous
  :: Homogeneous t => (a -> a -> b) -> t a -> t a -> Maybe (t b)
zipWithHomogeneous f x y =
  zipHomogeneous (\(Par1 a :*: Par1 b) -> Just (f a b)) (Par1 x :*: Par1 y)

{- | Zip three `Homogeneous` structures, when they have the same shape.

>>> zipWithHomogeneous3 (\a b c -> a + b + c) [1, 2] [3, 4] [5, 6 :: Int]
Just [9,12]
>>> zipWithHomogeneous3 (\a b c -> a + b + c) [1, 2] [3, 4] [5 :: Int]
Nothing
-}
zipWithHomogeneous3
  :: Homogeneous t
  => (a -> a -> a -> b) -> t a -> t a -> t a -> Maybe (t b)
zipWithHomogeneous3 f x y z = zipHomogeneous
  (\(Par1 a :*: Par1 b :*: Par1 c) -> Just (f a b c))
  (Par1 x :*: Par1 y :*: Par1 z)

{- | Zip two `Homogeneous` structures by an action, when they have the same
shape. The actions of the positions which match run, even when the shapes
differ elsewhere.

>>> zipWithHomogeneousM (\a b -> ([a + b], a * b)) [1, 2] [3, 4 :: Int]
([4,6],Just [3,8])
>>> zipWithHomogeneousM (\a b -> ([a + b], a * b)) [1, 2] [3 :: Int]
([4],Nothing)
-}
zipWithHomogeneousM
  :: (Homogeneous t, Applicative m)
  => (a -> a -> m b) -> t a -> t a -> m (Maybe (t b))
zipWithHomogeneousM f x y = runStar
  (runZipporah (homogeneously (Zipporah (Star
    (\(Par1 a :*: Par1 b) -> Just <$> f a b)))))
  (Par1 x :*: Par1 y)

{- | Transpose `Homogeneous` structures in the positions of a `Traversable`,
when they have the same shape. Without any structures, a sum's first copy
repeats, so that a list is infinite.

>>> transposeHomogeneous [[1, 2, 3], [4, 5, 6 :: Int]]
Just [[1,4],[2,5],[3,6]]
>>> transposeHomogeneous [[1, 2], [3 :: Int]]
Nothing
-}
transposeHomogeneous
  :: (Homogeneous t, Traversable f) => f (t a) -> Maybe (t (f a))
transposeHomogeneous = zipHomogeneous Just


{- | t'Zipporah' is a profunctor @p@ between functors, like `Data.Bifunctor.Biff`,
but lifting @p@'s instances through @g@, & splitting sums by @f@,
which fail in @g@ unless every position of @f@ holds the same copy.
-}
newtype Zipporah p f g a b = Zipporah {runZipporah :: p (f a) (g b)}
instance (Profunctor p, Functor f, Functor g)
  => Profunctor (Zipporah p f g) where
    dimap h k (Zipporah x) = Zipporah (dimap (fmap h) (fmap k) x)
instance (Profunctor p, Functor g) => Functor (Zipporah p f g a) where
  fmap k (Zipporah x) = Zipporah (rmap (fmap k) x)
instance (Monoidal p, Applicative g) => Applicative (Zipporah p f g a) where
  pure b = Zipporah (pure (pure b))
  Zipporah x <*> Zipporah y = Zipporah (liftA2 (<*>) x y)
instance (Monoidal p, Alternative g) => Alternative (Zipporah p f g a) where
  empty = Zipporah (pure empty)
  Zipporah x <|> Zipporah y = Zipporah (liftA2 (<|>) x y)
instance Monadic p => Monad (Zipporah p f Maybe a) where
  Zipporah x >>= k = Zipporah (x >>= maybe (pure Nothing) (runZipporah . k))
instance (Profunctor p, Filterable g) => Filterable (Zipporah p f g a) where
  mapMaybe h (Zipporah x) = Zipporah (rmap (mapMaybe h) x)
instance (Monoidal p, Alternative g) => DisjunctiveMonoid (Zipporah p f g a b) where
  falseP = empty
  (>|<) = (<|>)
instance (Choice p, Traversable f, Alternative g) => Choice (Zipporah p f g) where
  left' (Zipporah x) = Zipporah (leftCopies x)
  right' (Zipporah x) = Zipporah (rightCopies x)
instance (Profunctor p, Functor f, Filterable g) => Cochoice (Zipporah p f g) where
  unleft (Zipporah x) =
    Zipporah (dimap (fmap Left) (mapMaybe (either Just (const Nothing))) x)
  unright (Zipporah x) =
    Zipporah (dimap (fmap Right) (mapMaybe (either (const Nothing) Just)) x)
instance (Choice p, Monoidal p, Traversable f, Alternative g)
  => CocartesianMonoidal (Zipporah p f g) where
    zeroP = empty
    Zipporah x >+< Zipporah y = Zipporah (liftA2 (<|>) (leftCopies x) (rightCopies y))
instance (Choice p, Monoidal p, Traversable f, Alternative g)
  => CocartesianChoice (Zipporah p f g) where
    alternate = Zipporah . either leftCopies rightCopies . bimap runZipporah runZipporah
instance (Choice p, Monoidal p, Traversable f, Alternative g)
  => Distributor (Zipporah p f g)
instance (Choice p, Monoidal p, Traversable f, Alternative g)
  => Alternator (Zipporah p f g)

-- Sources which all hold the left copy of a sum, or else fail.
leftCopies
  :: (Choice p, Traversable f, Alternative g)
  => p (f a) (g b) -> p (f (Either a c)) (g (Either b d))
leftCopies = dimap
  (\ss -> maybe (Right ()) Left (traverse (either Just (const Nothing)) ss))
  (either (fmap Left) (const empty))
  . left'

-- Sources which all hold the right copy of a sum, or else fail.
rightCopies
  :: (Choice p, Traversable f, Alternative g)
  => p (f c) (g d) -> p (f (Either a c)) (g (Either b d))
rightCopies = dimap
  (\ss -> maybe (Right ()) Left (traverse (either (const Nothing) Just) ss))
  (either (fmap Right) (const empty))
  . left'
