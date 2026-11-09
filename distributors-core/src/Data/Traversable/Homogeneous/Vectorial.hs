{-|
Module      : Data.Traversable.Homogeneous.Vectorial
Description : vectorial
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Data.Traversable.Homogeneous.Vectorial
  ( -- * Vectorial
    Vectorial
  , vectorially
    -- * Basis
  , _Basis
  , basisVectorial
  , ordinalVectorial
  , fromOrdinalVectorial
  , dimensionVectorial
  , coordinate
    -- * Zipping
  , zipVectorial
  , zipWithVectorial
  , zipWithVectorial'
  , zipWith3Vectorial
  , zipWith3Vectorial'
  , unzipVectorial
  , transposeVectorial
  , fromListVectorial
    -- * Vector space
  , zeroVectorial
  , unitVectorial
  , (^+^)
  , (^-^)
  , negateVectorial
  , (*^)
  , dotVectorial
    -- * Matrices
  , identityVectorial
  , outerVectorial
  , (!*)
  , (!*!)
  ) where

import Control.Lens (Lens', dimap, lens)
import Control.Lens.Comonocle (Comonocle)
import Data.Foldable (toList)
import Data.Functor.Rep (Representable (..))
import Data.List (elemIndex, genericDrop, genericLength)
import Data.Maybe (listToMaybe)
import Data.Profunctor.Monoidal (Monoidal, ditraverse)
import Data.Profunctor.Monoidal.Cocartesian (CocartesianMonoidal (..), dialt)
import Data.Void (absurd)
import Data.Traversable (mapAccumL)
import Data.Traversable.Homogeneous
import Numeric.Natural (Natural)

-- $setup
-- >>> import Control.Lens (over, view)
-- >>> import Data.Complex

{- | `Vectorial` containers are `Homogeneous` & `Representable`:
`Representable` gives them a basis, `Rep` @f@, of the positions
of their every value, & `Homogeneous`, by its `Foldable` order,
enumerates that basis, so that it's countable, as `basisVectorial`.

> prop> toList v = map (index v) basisVectorial

So they zip & transpose totally, as `Homogeneous` structures of
different shapes can't, & they're sequenced by `Monoidal`
`Data.Profunctor.Profunctor`s alone, `vectorially`,
which `homogeneously` specializes.

> prop> homogeneously = vectorially
-}
type Vectorial f = (Homogeneous f, Representable f)

-- | Sequences an action in every position, by `ditraverse`.
vectorially :: (Vectorial f, Monoidal p) => p a b -> p (f a) (f b)
vectorially = ditraverse

{- | The `Comonocle` of the basis, as a sum of copies of @()@,
one for each basis element, in `Foldable` order, so that
the `Comonocle` combinators navigate it.

>>> import Control.Lens.Comonocle
>>> countComonocle (_Basis @Complex)
2
>>> toEnumComonocle (_Basis @Complex) () 1
Just True
>>> enumerateComonocle (_Basis @Complex) False
[False,True]
-}
_Basis :: forall f. (Vectorial f, Eq (Rep f)) => Comonocle (Rep f) (Rep f) () ()
_Basis p = case basisVectorial @f of
  -- an empty basis has no elements, by the law of `Vectorial`
  [] -> dimap (\_ -> error "_Basis: no basis elements") absurd zeroP
  r : rs -> copies r rs
  where
    copies r = \case
      [] -> dimap (const ()) (fmap (const r)) p
      r' : rs ->
        dialt (\s -> if s == r then Left () else Right s)
          (fmap (const r)) id p (copies r' rs)

-- | The basis, in `Foldable` order.
--
-- >>> basisVectorial @Complex
-- [False,True]
basisVectorial :: forall f. Vectorial f => [Rep f]
basisVectorial = toList (tabulate @f id)

-- | The ordinal of a basis element, in `basisVectorial`, numbered from 0.
--
-- >>> ordinalVectorial @Complex True
-- Just 1
ordinalVectorial
  :: forall f. (Vectorial f, Eq (Rep f)) => Rep f -> Maybe Natural
ordinalVectorial i = fromIntegral <$> elemIndex i (basisVectorial @f)

-- | The basis element of an ordinal, if there is one.
--
-- >>> fromOrdinalVectorial @Complex 1
-- Just True
-- >>> fromOrdinalVectorial @Complex 2
-- Nothing
fromOrdinalVectorial :: forall f. Vectorial f => Natural -> Maybe (Rep f)
fromOrdinalVectorial n = listToMaybe (genericDrop n (basisVectorial @f))

-- | The number of basis elements, which diverges for an infinite basis.
--
-- >>> dimensionVectorial @Complex
-- 2
dimensionVectorial :: forall f. Vectorial f => Natural
dimensionVectorial = genericLength (basisVectorial @f)

-- | The coordinate at a basis element.
--
-- >>> view (coordinate True) (1 :+ 2)
-- 2
-- >>> over (coordinate False) negate (1 :+ 2)
-- (-1) :+ 2
coordinate :: (Representable f, Eq (Rep f)) => Rep f -> Lens' (f a) a
coordinate i = lens (`index` i) $ \v a ->
  tabulate (\j -> if j == i then a else index v j)

-- | Zip two structures, coordinate by coordinate.
--
-- >>> zipVectorial (1 :+ 2) ('a' :+ 'b')
-- (1,'a') :+ (2,'b')
zipVectorial :: Representable f => f a -> f b -> f (a, b)
zipVectorial = zipWithVectorial (,)

-- | Zip two structures by a function, coordinate by coordinate.
--
-- >>> zipWithVectorial (+) (1 :+ 2) (10 :+ 20)
-- 11 :+ 22
zipWithVectorial :: Representable f => (a -> b -> c) -> f a -> f b -> f c
zipWithVectorial f as bs = tabulate (\i -> f (index as i) (index bs i))

-- | `zipWithVectorial`, evaluating every coordinate, in `Foldable` order.
zipWithVectorial' :: Vectorial f => (a -> b -> c) -> f a -> f b -> f c
zipWithVectorial' f as bs = forced (zipWithVectorial f as bs)

-- | Zip three structures by a function, coordinate by coordinate.
--
-- >>> zipWith3Vectorial (\a b c -> a + b * c) (1 :+ 2) (3 :+ 4) (5 :+ 6)
-- 16 :+ 26
zipWith3Vectorial
  :: Representable f => (a -> b -> c -> d) -> f a -> f b -> f c -> f d
zipWith3Vectorial f as bs cs =
  tabulate (\i -> f (index as i) (index bs i) (index cs i))

-- | `zipWith3Vectorial`, evaluating every coordinate, in `Foldable` order.
zipWith3Vectorial'
  :: Vectorial f => (a -> b -> c -> d) -> f a -> f b -> f c -> f d
zipWith3Vectorial' f as bs cs = forced (zipWith3Vectorial f as bs cs)

-- | Unzip a structure of pairs.
--
-- >>> unzipVectorial ((1,'a') :+ (2,'b'))
-- (1 :+ 2,'a' :+ 'b')
unzipVectorial :: Functor f => f (a, b) -> (f a, f b)
unzipVectorial abs' = (fst <$> abs', snd <$> abs')

-- | Transpose nested structures.
--
-- >>> transposeVectorial ((1 :+ 2) :+ (3 :+ 4))
-- (1 :+ 3) :+ (2 :+ 4)
transposeVectorial
  :: (Representable f, Representable g) => f (g a) -> g (f a)
transposeVectorial xss =
  tabulate (\j -> tabulate (\i -> index (index xss i) j))

{- | A structure of a list's values, in `Foldable` order, when it has
exactly as many as the basis.

>>> fromListVectorial "ab" :: Maybe (Complex Char)
Just ('a' :+ 'b')
>>> fromListVectorial "abc" :: Maybe (Complex Char)
Nothing
-}
fromListVectorial :: forall f a. Vectorial f => [a] -> Maybe (f a)
fromListVectorial as = case mapAccumL fill as (tabulate @f (const ())) of
  ([], filled) -> sequenceA filled
  _ -> Nothing
  where
    fill (x : xs) () = (xs, Just x)
    fill [] () = ([], Nothing)

-- | The zero vector.
zeroVectorial :: (Representable f, Num a) => f a
zeroVectorial = tabulate (const 0)

-- | The unit vector of a basis element.
--
-- >>> unitVectorial True :: Complex Int
-- 0 :+ 1
unitVectorial :: (Representable f, Eq (Rep f), Num a) => Rep f -> f a
unitVectorial i = tabulate (\j -> if i == j then 1 else 0)

-- | Add vectors, strictly.
(^+^) :: (Vectorial f, Num a) => f a -> f a -> f a
(^+^) = zipWithVectorial' (+)
infixl 6 ^+^

-- | Subtract vectors, strictly.
(^-^) :: (Vectorial f, Num a) => f a -> f a -> f a
(^-^) = zipWithVectorial' (-)
infixl 6 ^-^

-- | Negate a vector, strictly.
negateVectorial :: (Vectorial f, Num a) => f a -> f a
negateVectorial = forced . fmap negate

-- | Scale a vector, strictly.
--
-- >>> 2 *^ (1 :+ 2)
-- 2 :+ 4
(*^) :: (Vectorial f, Num a) => a -> f a -> f a
s *^ v = forced (fmap (s *) v)
infixl 7 *^

-- | The dot product of vectors, summed strictly.
--
-- >>> dotVectorial (1 :+ 2) (3 :+ 4)
-- 11
dotVectorial :: (Vectorial f, Num a) => f a -> f a -> a
dotVectorial u v = foldl' (+) 0 (zipWithVectorial (*) u v)

-- | The identity matrix, of rows of unit vectors.
--
-- >>> identityVectorial :: Complex (Complex Int)
-- (1 :+ 0) :+ (0 :+ 1)
identityVectorial :: (Representable f, Eq (Rep f), Num a) => f (f a)
identityVectorial = tabulate unitVectorial

-- | The outer product of vectors, a matrix of rows.
--
-- >>> outerVectorial (1 :+ 2) (3 :+ 4)
-- (3 :+ 4) :+ (6 :+ 8)
outerVectorial
  :: (Representable f, Representable g, Num a) => f a -> g a -> f (g a)
outerVectorial u v = fmap (\a -> fmap (a *) v) u

-- | Multiply a matrix, of rows, by a vector.
--
-- >>> ((1 :+ 2) :+ (3 :+ 4)) !* (1 :+ 1)
-- 3 :+ 7
(!*) :: (Vectorial f, Vectorial g, Num a) => f (g a) -> g a -> f a
m !* v = forced (fmap (`dotVectorial` v) m)
infixl 7 !*

-- | Multiply matrices, of rows.
--
-- >>> ((1 :+ 2) :+ (3 :+ 4)) !*! ((0 :+ 1) :+ (1 :+ 0))
-- (2 :+ 1) :+ (4 :+ 3)
(!*!)
  :: (Vectorial f, Vectorial g, Vectorial h, Num a)
  => f (g a) -> g (h a) -> f (h a)
m !*! n = fmap (transposeVectorial n !*) m
infixl 7 !*!

-- | A structure, with every value evaluated, in `Foldable` order.
forced :: Foldable f => f a -> f a
forced xs = foldr seq xs xs
