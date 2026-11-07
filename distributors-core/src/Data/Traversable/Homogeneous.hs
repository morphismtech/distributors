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
  , zipWithHomogeneous
  , zipWithHomogeneous3
    -- * Enumerable
  , Enumerable (..)
  , extractEnumerable
  , indexEnumerable
  , Bool1 (..), bool1
    -- * Counting & Zipping
  , Counting (..)
  , Zipping (..)
  , MultiZipping (..)
  ) where

import Control.Applicative
import Control.Lens hiding (chosen)
import Control.Lens.PartialIso
import Control.Monad ((>=>))
import Control.Monad.Trans.Identity (IdentityT (..))
import Data.Bool
import Data.Complex
import Data.Functor.Compose
import qualified Data.Functor.Product as Functor
import qualified Data.Functor.Sum as Functor
import qualified Data.Monoid as Monoid
import Data.Ord (Down (..))
import qualified Data.Semigroup as Semigroup
import Data.Monoid.Disjunctive
import Data.Profunctor (Cochoice (..), Forget (..))
import Data.Profunctor.Monoidal
import Data.Proxy
import Data.Sequence (Seq)
import Data.Tagged
import Data.Tree (Tree (..))
import Data.Vector (Vector)
import Data.Void
import GHC.Generics
import Numeric.Natural (Natural)
import Witherable (Filterable (..))

import Data.Profunctor.Distributor
import Data.Profunctor.Monoidal.Cocartesian

{- | A class of `Homogeneous`
countable sums of countable products.
-}
class Traversable t => Homogeneous t where
  {- | Sequences actions `homogeneously`.

  @prop> homogeneously @Maybe = optionalP@
  @prop> homogeneously @[] = manyP@

  Any `Traversable` & `Data.Distributive.Distributive` countable product
  can be given a default implementation for the `homogeneously` method
  with `ditraverse`.

  @prop> homogeneously = ditraverse@

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

@prop> enumerably @Identity = dimap runIdentity Identity@

Every `Enumerable` is sequenced `enumerably` as it's sequenced
`homogeneously`, by a `Distributor`.

@prop> enumerably = homogeneously@

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
{- | A copy tagged by a finite enumeration is a copy for each tag,
numbered by its tag's `fromEnum`, from `minBound`,
& summed in a balanced tree, built lazily.

>>> map indexEnumerable [(False, 'a'), (True, 'b')]
[0,1]
>>> map indexEnumerable [(LT, 'a'), (EQ, 'b'), (GT, 'c')]
[0,1,2]
>>> zipWithHomogeneous (+) (True, 1) (True, 2 :: Int)
Just (True,3)
>>> zipWithHomogeneous (+) (True, 1) (False, 2 :: Int)
Nothing

Reaching a copy takes time logarithmic in the number of tags,
but counting them, as `indexEnumerable` does, takes time linear in it,
so it never ends for @Int@, & tags whose `fromEnum` fails, like large
@Word@s, aren't enumerable.
-}
instance (Enum e, Bounded e) => Homogeneous ((,) e) where
  homogeneously = enumerably
instance (Enum e, Bounded e) => Enumerable ((,) e) where
  enumerably p = go (tag (minBound :: e)) (tag (maxBound :: e))
    where
      tag = toInteger . fromEnum
      go lo hi
        | lo >= hi = dimap snd (toEnum (fromInteger lo),) p
        | otherwise = dialt
            (\ea -> if tag (fst ea) <= mid then Left ea else Right ea)
            id id (go lo mid) (go (mid + 1) hi)
        where
          mid = (lo + hi) `div` 2

-- | The copy which an `Enumerable` sum holds.
extractEnumerable :: Enumerable f => f a -> a
extractEnumerable = runForget (enumerably (Forget id))

-- | Which copy an `Enumerable` sum holds, numbered from 0, left to right.
indexEnumerable :: Enumerable f => f a -> Natural
indexEnumerable =
  case enumerably (Counting 1 (const 0)) of Counting _ which -> which

{- | Zip two `Homogeneous` structures, when they have the same shape.

>>> zipWithHomogeneous (+) [1, 2] [3, 4 :: Int]
Just [4,6]
>>> zipWithHomogeneous (+) [1] [3, 4 :: Int]
Nothing
-}
zipWithHomogeneous
  :: Homogeneous t => (a -> a -> b) -> t a -> t a -> Maybe (t b)
zipWithHomogeneous f =
  runZipping (homogeneously (Zipping (\a0 a1 -> Just (f a0 a1))))

{- | Zip three `Homogeneous` structures, when they have the same shape.

>>> zipWithHomogeneous3 (\a b c -> a + b + c) [1, 2] [3, 4] [5, 6 :: Int]
Just [9,12]
>>> zipWithHomogeneous3 (\a b c -> a + b + c) [1, 2] [3, 4] [5 :: Int]
Nothing
-}
zipWithHomogeneous3
  :: Homogeneous t
  => (a -> a -> a -> b) -> t a -> t a -> t a -> Maybe (t b)
zipWithHomogeneous3 f x y z = runMultiZipping
  (homogeneously (MultiZipping
    (\(Par1 a :*: Par1 b :*: Par1 c) -> Just (f a b c))))
  (Par1 x :*: Par1 y :*: Par1 z)

{- | `Counting` counts the index of an `Enumerable`. -}
data Counting s t = Counting Natural (s -> Natural)
instance Profunctor Counting where
  dimap f _ (Counting count which) = Counting count (which . f)
instance Functor (Counting s) where
  fmap _ (Counting count which) = Counting count which
instance Contravariant (Counting s) where
  contramap _ (Counting count which) = Counting count which
instance Applicative (Counting s) where
  pure _ = Counting 1 (const 0)
  Counting count0 which0 <*> Counting count1 which1 = Counting
    (count0 * count1)
    (\s -> which0 s * count1 + which1 s)
instance CocartesianMonoidal Counting where
  zeroP = Counting 0 absurd
  Counting count0 which0 >+< Counting count1 which1 = Counting
    (count0 + count1)
    (either which0 ((count0 +) . which1))
instance Cochoice Counting where
  unleft (Counting count which) = Counting count (which . Left)
  unright (Counting count which) = Counting count (which . Right)

-- | `Zipping` zips two sources, when they have the same shape.
newtype Zipping s t = Zipping {runZipping :: s -> s -> Maybe t}
instance Profunctor Zipping where
  dimap f g (Zipping z) = Zipping (\s0 s1 -> g <$> z (f s0) (f s1))
instance Functor (Zipping s) where
  fmap = rmap
instance Applicative (Zipping s) where
  pure t = Zipping (\_ _ -> Just t)
  Zipping zf <*> Zipping zx = Zipping (\s0 s1 -> zf s0 s1 <*> zx s0 s1)
instance Alternative (Zipping s) where
  empty = Zipping (\_ _ -> Nothing)
  Zipping z0 <|> Zipping z1 = Zipping (\s0 s1 -> z0 s0 s1 <|> z1 s0 s1)
instance Monad (Zipping s) where
  Zipping z >>= f = Zipping (\s0 s1 -> z s0 s1 >>= \t -> runZipping (f t) s0 s1)
instance Filterable (Zipping s) where
  mapMaybe f (Zipping z) = Zipping (\s0 s1 -> z s0 s1 >>= f)
instance DisjunctiveMonoid (Zipping s t)
instance Choice Zipping where
  left' (Zipping z) = Zipping $ \s0 s1 -> case (s0, s1) of
    (Left a0, Left a1) -> Left <$> z a0 a1
    _ -> Nothing
  right' (Zipping z) = Zipping $ \s0 s1 -> case (s0, s1) of
    (Right a0, Right a1) -> Right <$> z a0 a1
    _ -> Nothing
instance Cochoice Zipping where
  unleft (Zipping z) = Zipping $ \a0 a1 ->
    z (Left a0) (Left a1) >>= either Just (const Nothing)
  unright (Zipping z) = Zipping $ \a0 a1 ->
    z (Right a0) (Right a1) >>= either (const Nothing) Just
instance CocartesianMonoidal Zipping where
  zeroP = Zipping absurd
  Zipping z0 >+< Zipping z1 = Zipping $ \case
    Left s0 -> either (fmap Left . z0 s0) (const Nothing)
    Right s1 -> either (const Nothing) (fmap Right . z1 s1)
instance CocartesianChoice Zipping
instance Distributor Zipping
instance Alternator Zipping

{- | `MultiZipping` zips sources in the positions of a `Traversable`,
like `Complex` of 2, when they have the same shape, as `Zipping` zips two.
With no sources, a sum is its first copy.
-}
newtype MultiZipping f s t = MultiZipping {runMultiZipping :: f s -> Maybe t}
instance Functor f => Profunctor (MultiZipping f) where
  dimap f g (MultiZipping z) = MultiZipping (fmap g . z . fmap f)
instance Functor (MultiZipping f s) where
  fmap g (MultiZipping z) = MultiZipping (fmap g . z)
instance Applicative (MultiZipping f s) where
  pure t = MultiZipping (\_ -> Just t)
  MultiZipping zf <*> MultiZipping zx = MultiZipping (\ss -> zf ss <*> zx ss)
instance Alternative (MultiZipping f s) where
  empty = MultiZipping (\_ -> Nothing)
  MultiZipping z0 <|> MultiZipping z1 = MultiZipping (\ss -> z0 ss <|> z1 ss)
instance Monad (MultiZipping f s) where
  MultiZipping z >>= k =
    MultiZipping (\ss -> z ss >>= \t -> runMultiZipping (k t) ss)
instance Filterable (MultiZipping f s) where
  mapMaybe f (MultiZipping z) = MultiZipping (z >=> f)
instance DisjunctiveMonoid (MultiZipping f s t) where
  falseP = empty
  (>|<) = (<|>)
instance Traversable f => Choice (MultiZipping f) where
  left' (MultiZipping z) = MultiZipping $ \ss ->
    Left <$> (traverse (either Just (const Nothing)) ss >>= z)
  right' (MultiZipping z) = MultiZipping $ \ss ->
    Right <$> (traverse (either (const Nothing) Just) ss >>= z)
instance Functor f => Cochoice (MultiZipping f) where
  unleft (MultiZipping z) = MultiZipping $ \ss ->
    z (Left <$> ss) >>= either Just (const Nothing)
  unright (MultiZipping z) = MultiZipping $ \ss ->
    z (Right <$> ss) >>= either (const Nothing) Just
instance Traversable f => CocartesianMonoidal (MultiZipping f) where
  zeroP = empty
  MultiZipping z0 >+< MultiZipping z1 = MultiZipping $ \ss ->
    Left <$> (traverse (either Just (const Nothing)) ss >>= z0)
    <|> Right <$> (traverse (either (const Nothing) Just) ss >>= z1)
instance Traversable f => CocartesianChoice (MultiZipping f)
instance Traversable f => Distributor (MultiZipping f)
instance Traversable f => Alternator (MultiZipping f)
