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
    -- * Enumerable
  , Enumerable (..)
  , extractEnumerable
  , fromEnumerable
  , toEnumerable
  , succEnumerable
  , predEnumerable
  , enumerateFrom
    -- * Indexing & Zipporah
  , Indexing (..)
  , Zipporah (..)
  ) where

import Control.Applicative
import Control.Lens hiding (chosen)
import Control.Lens.PartialIso
import Control.Monad ((>=>))
import Control.Monad.Trans.Identity (IdentityT (..))
import Data.Complex
import Data.Functor.Compose
import qualified Data.Functor.Product as Functor
import qualified Data.Functor.Sum as Functor
import qualified Data.Monoid as Monoid
import Data.Ord (Down (..))
import qualified Data.Semigroup as Semigroup
import Data.Monoid.Disjunctive
import Data.Profunctor (Cochoice (..), Forget (..), Star (..))
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

{- | A class of `Enumerable` countable sums of single copies,
which are `Homogeneous`, & sequenced by sums alone.

> prop> enumerably @Identity = dimap runIdentity Identity

Every `Enumerable` is sequenced `enumerably` as it's sequenced
`homogeneously`, by a `Distributor`.

> prop> enumerably = homogeneously

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

>>> map fromEnumerable [(False, 'a'), (True, 'b')]
[0,1]
>>> map fromEnumerable [(LT, 'a'), (EQ, 'b'), (GT, 'c')]
[0,1,2]
>>> zipWithHomogeneous (+) (True, 1) (True, 2 :: Int)
Just (True,3)
>>> zipWithHomogeneous (+) (True, 1) (False, 2 :: Int)
Nothing

Reaching a copy takes time logarithmic in the number of tags,
but counting them, as `fromEnumerable` does, takes time linear in it,
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

{- | Which copy an `Enumerable` sum holds, numbered from 0, left to right,
like `fromEnum`.

>>> fromEnumerable (GT, 'x')
2
-}
fromEnumerable :: Enumerable f => f a -> Natural
fromEnumerable =
  case enumerably (pure ()) of Indexing _ which _ -> which

{- | The copy of an `Enumerable` sum at an index, if there is one,
like `toEnum`, the inverse of `fromEnumerable`.

>>> [toEnumerable 'x' i | i <- [0..3]] :: [Maybe (Ordering, Char)]
[Just (LT,'x'),Just (EQ,'x'),Just (GT,'x'),Nothing]

-}
toEnumerable :: Enumerable f => a -> Natural -> Maybe (f a)
toEnumerable a copy =
  case enumerably (pure a) of Indexing _ _ select -> select copy

{- | The next copy of an `Enumerable` sum, if there is one, like `succ`.

>>> succEnumerable (EQ, 'x')
Just (GT,'x')
>>> succEnumerable (GT, 'x')
Nothing
-}
succEnumerable :: Enumerable f => f a -> Maybe (f a)
succEnumerable x = case enumerably (pure (extractEnumerable x)) of
  Indexing _ which select -> select (which x + 1)

{- | The previous copy of an `Enumerable` sum, if there is one, like `pred`.

>>> predEnumerable (EQ, 'x')
Just (LT,'x')
>>> predEnumerable (LT, 'x')
Nothing
-}
predEnumerable :: Enumerable f => f a -> Maybe (f a)
predEnumerable x = case enumerably (pure (extractEnumerable x)) of
  Indexing _ which select -> case which x of
    0 -> Nothing
    copy -> select (copy - 1)

{- | The copies of an `Enumerable` sum from one onward, like `enumFrom`.

>>> enumerateFrom (EQ, 'x')
[(EQ,'x'),(GT,'x')]
-}
enumerateFrom :: Enumerable f => f a -> [f a]
enumerateFrom x = case enumerably (pure (extractEnumerable x)) of
  Indexing _ which select ->
    let go copy = maybe [] (: go (copy + 1)) (select copy) in go (which x)

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


{- | `Indexing` numbers the copies of a sum of products, from 0,
left to right, & products row by row, both ways:
how many copies there are, which copy a source is, & the copy at an index.
-}
data Indexing s t = Indexing Natural (s -> Natural) (Natural -> Maybe t)
instance Profunctor Indexing where
  dimap f g (Indexing count which select) =
    Indexing count (which . f) (fmap g . select)
instance Functor (Indexing s) where
  fmap = rmap
instance Applicative (Indexing s) where
  pure t = Indexing 1 (const 0) (\i -> if i == 0 then Just t else Nothing)
  Indexing count0 which0 select0 <*> Indexing count1 which1 select1 = Indexing
    (count0 * count1)
    (\s -> which0 s * count1 + which1 s)
    (\i -> if count1 == 0 then Nothing
      else select0 (i `div` count1) <*> select1 (i `mod` count1))
instance CocartesianMonoidal Indexing where
  zeroP = Indexing 0 absurd (const Nothing)
  Indexing count0 which0 select0 >+< Indexing count1 which1 select1 = Indexing
    (count0 + count1)
    (either which0 ((count0 +) . which1))
    (\i -> if i < count0 then Left <$> select0 i
      else Right <$> select1 (i - count0))
instance Cochoice Indexing where
  unleft (Indexing count which select) = Indexing count
    (which . Left) (select >=> either Just (const Nothing))
  unright (Indexing count which select) = Indexing count
    (which . Right) (select >=> either (const Nothing) Just)


{- | `Zipporah` is a profunctor @p@ between functors, like `Data.Bifunctor.Biff`,
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
