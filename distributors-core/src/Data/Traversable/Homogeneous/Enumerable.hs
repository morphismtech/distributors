{-|
Module      : Data.Traversable.Homogeneous.Enumerable
Description : enumerable
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Data.Traversable.Homogeneous.Enumerable
  ( -- * Enumerable
    Enumerable (..)
  , extractEnumerable
  , fromEnumerable
  , toEnumerable
  , succEnumerable
  , predEnumerable
  , enumerateFrom
  , enumerateFromThen
  , enumerateFromTo
  , enumerateFromThenTo
    -- * Enumerator
  , Enumerator (..)
  ) where

import Control.Applicative
import Control.Lens hiding (chosen)
import Control.Monad ((>=>))
import Control.Monad.Trans.Identity (IdentityT (..))
import Data.Functor.Compose
import qualified Data.Functor.Sum as Functor
import qualified Data.Monoid as Monoid
import Data.Ord (Down (..))
import qualified Data.Semigroup as Semigroup
import Data.Profunctor (Cochoice (..), Forget (..))
import Data.Tagged
import Data.Void
import GHC.Generics
import Numeric.Natural (Natural)

import Data.Profunctor.Monoidal.Cocartesian
import Data.Traversable.Homogeneous

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

Reaching a copy takes time logarithmic in the number of tags,
but counting them, as `fromEnumerable` does, takes time linear in it,
so it never ends for @Int@, & tags whose `fromEnum` fails, like large
@Word@s, aren't enumerable.
-}
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
  case enumerably (pure ()) of Enumerator _ which _ -> which

{- | The copy of an `Enumerable` sum at an index, if there is one,
like `toEnum`, the inverse of `fromEnumerable`.

>>> [toEnumerable 'x' i | i <- [0..3]] :: [Maybe (Ordering, Char)]
[Just (LT,'x'),Just (EQ,'x'),Just (GT,'x'),Nothing]

-}
toEnumerable :: Enumerable f => a -> Natural -> Maybe (f a)
toEnumerable a copy =
  case enumerably (pure a) of Enumerator _ _ select -> select copy

{- | The next copy of an `Enumerable` sum, if there is one, like `succ`.

>>> succEnumerable (EQ, 'x')
Just (GT,'x')
>>> succEnumerable (GT, 'x')
Nothing
-}
succEnumerable :: Enumerable f => f a -> Maybe (f a)
succEnumerable x = case enumerably (pure (extractEnumerable x)) of
  Enumerator _ which select -> select (which x + 1)

{- | The previous copy of an `Enumerable` sum, if there is one, like `pred`.

>>> predEnumerable (EQ, 'x')
Just (LT,'x')
>>> predEnumerable (LT, 'x')
Nothing
-}
predEnumerable :: Enumerable f => f a -> Maybe (f a)
predEnumerable x = case enumerably (pure (extractEnumerable x)) of
  Enumerator _ which select -> case which x of
    0 -> Nothing
    copy -> select (copy - 1)

{- | The copies of an `Enumerable` sum from one onward, like `enumFrom`.

>>> enumerateFrom (EQ, 'x')
[(EQ,'x'),(GT,'x')]
-}
enumerateFrom :: Enumerable f => f a -> [f a]
enumerateFrom x = case enumerably (pure (extractEnumerable x)) of
  Enumerator _ which select ->
    let go copy = maybe [] (: go (copy + 1)) (select copy) in go (which x)

{- | The copies of an `Enumerable` sum from one onward, holding its focus,
stepping by the copy of another, like `enumFromThen`.

>>> enumerateFromThen (LT, 'x') (EQ, ())
[(LT,'x'),(EQ,'x'),(GT,'x')]
>>> enumerateFromThen (GT, 'x') (EQ, ())
[(GT,'x'),(EQ,'x'),(LT,'x')]
-}
enumerateFromThen :: Enumerable f => f a -> f b -> [f a]
enumerateFromThen x y = copiesAt x [from, fromEnumerable' y ..]
  where
    from = fromEnumerable' x

{- | The copies of an `Enumerable` sum from one to the copy of another,
holding its focus, like `enumFromTo`.

>>> enumerateFromTo (LT, 'x') (EQ, ())
[(LT,'x'),(EQ,'x')]
-}
enumerateFromTo :: Enumerable f => f a -> f b -> [f a]
enumerateFromTo x z = copiesAt x [fromEnumerable' x .. fromEnumerable' z]

{- | The copies of an `Enumerable` sum from one to the copy of another,
holding its focus, stepping by the copy of a third, like `enumFromThenTo`.

>>> enumerateFromThenTo (GT, 'x') (EQ, ()) (LT, ())
[(GT,'x'),(EQ,'x'),(LT,'x')]
-}
enumerateFromThenTo :: Enumerable f => f a -> f b -> f c -> [f a]
enumerateFromThenTo x y z =
  copiesAt x [fromEnumerable' x, fromEnumerable' y .. fromEnumerable' z]

-- | The index of an `Enumerable` sum's copy, as an `Integer`.
fromEnumerable' :: Enumerable f => f a -> Integer
fromEnumerable' = toInteger . fromEnumerable

{- | The copies at some indices, holding a sum's focus,
until an index has none.
-}
copiesAt :: Enumerable f => f a -> [Integer] -> [f a]
copiesAt x indices = case enumerably (pure (extractEnumerable x)) of
  Enumerator _ _ select ->
    let
      go = \case
        i : is | i >= 0, Just copy <- select (fromInteger i) -> copy : go is
        _ -> []
    in go indices

{- | t'Enumerator' numbers the copies of a sum of products, from 0,
left to right, & products row by row, both ways:
how many copies there are, which copy a source is, & the copy at an index.
-}
data Enumerator s t = Enumerator Natural (s -> Natural) (Natural -> Maybe t)
instance Profunctor Enumerator where
  dimap f g (Enumerator count which select) =
    Enumerator count (which . f) (fmap g . select)
instance Functor (Enumerator s) where
  fmap = rmap
instance Applicative (Enumerator s) where
  pure t = Enumerator 1 (const 0) (\i -> if i == 0 then Just t else Nothing)
  Enumerator count0 which0 select0 <*> Enumerator count1 which1 select1 = Enumerator
    (count0 * count1)
    (\s -> which0 s * count1 + which1 s)
    (\i -> if count1 == 0 then Nothing
      else select0 (i `div` count1) <*> select1 (i `mod` count1))
instance CocartesianMonoidal Enumerator where
  zeroP = Enumerator 0 absurd (const Nothing)
  Enumerator count0 which0 select0 >+< Enumerator count1 which1 select1 = Enumerator
    (count0 + count1)
    (either which0 ((count0 +) . which1))
    (\i -> if i < count0 then Left <$> select0 i
      else Right <$> select1 (i - count0))
instance Cochoice Enumerator where
  unleft (Enumerator count which select) = Enumerator count
    (which . Left) (select >=> either Just (const Nothing))
  unright (Enumerator count which select) = Enumerator count
    (which . Right) (select >=> either (const Nothing) Just)
