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
    -- * Shape
  , replicateVectorial
  , positionsVectorial
  , dimensionVectorial
    -- * Zipping
  , zipVectorial
  , zipWithVectorial
  , zipWithVectorial'
  , zipWith3Vectorial
  , zipWith3Vectorial'
  , unzipVectorial
  , transposeVectorial
    -- * Positions
  , fromListVectorial
  , indexVectorial
  , adjustVectorial
    -- * Vector space
  , zeroVectorial
  , (^+^)
  , (^-^)
  , negateVectorial
  , (*^)
  , dotVectorial
  ) where

import Data.Distributive (Distributive (..), cotraverse)
import Data.Foldable (toList)
import Data.Functor.Const (Const (..))
import Data.List (genericDrop, genericLength)
import Data.Maybe (listToMaybe)
import Data.Profunctor.Monoidal (Monoidal, ditraverse)
import Data.Traversable (mapAccumL)
import Data.Traversable.Homogeneous
import GHC.Generics (Par1 (..), (:*:) (..))
import Numeric.Natural (Natural)

-- $setup
-- >>> import Data.Complex
-- >>> import Data.Functor.Identity
-- >>> import Numeric.Natural (Natural)

{- | `Vectorial` containers are `Homogeneous` & `Data.Distributive.Distributive`,
so every value has the same shape, a fixed number of positions,
like `Data.Functor.Identity.Identity`, `Data.Complex.Complex`,
& their products & compositions. So they zip totally, as
`Homogeneous` structures of different shapes can't,
& they're sequenced by `Monoidal` `Data.Profunctor.Profunctor`s alone,
`vectorially`, which `homogeneously` specializes.

> prop> homogeneously = vectorially
-}
type Vectorial f = (Homogeneous f, Distributive f)

-- | Sequences an action in every position, by `ditraverse`.
vectorially :: (Vectorial f, Monoidal p) => p a b -> p (f a) (f b)
vectorially = ditraverse

-- | The same value in every position, like `pure`.
--
-- >>> replicateVectorial 'x' :: Complex Char
-- 'x' :+ 'x'
replicateVectorial :: forall f a. Vectorial f => a -> f a
replicateVectorial a = getConst <$> distribute (Const a :: Const a (f ()))

-- | Positions, numbered from 0, left to right.
--
-- >>> positionsVectorial :: Complex Natural
-- 0 :+ 1
positionsVectorial :: forall f. Vectorial f => f Natural
positionsVectorial =
  snd (mapAccumL (\i () -> (i + 1, i)) 0 (replicateVectorial @f ()))

-- | The number of positions.
--
-- >>> dimensionVectorial @Complex
-- 2
dimensionVectorial :: forall f. Vectorial f => Natural
dimensionVectorial = genericLength (toList (replicateVectorial @f ()))

-- | Zip two structures, position by position.
--
-- >>> zipVectorial (1 :+ 2) ('a' :+ 'b')
-- (1,'a') :+ (2,'b')
zipVectorial :: Vectorial f => f a -> f b -> f (a, b)
zipVectorial = zipWithVectorial (,)

{- | Zip two structures by a function, position by position,
which, as their shapes are the same, never fails.

>>> zipWithVectorial (+) (1 :+ 2) (10 :+ 20)
11 :+ 22
-}
zipWithVectorial :: Vectorial f => (a -> b -> c) -> f a -> f b -> f c
zipWithVectorial f as bs =
  cotraverse zipped (Par1 (Left <$> as) :*: Par1 (Right <$> bs))
  where
    -- positions agree, as shapes do
    zipped = \case
      Par1 (Left a) :*: Par1 (Right b) -> f a b
      _ -> error "zipWithVectorial: positions disagree"

-- | `zipWithVectorial`, evaluating every result, left to right.
zipWithVectorial' :: Vectorial f => (a -> b -> c) -> f a -> f b -> f c
zipWithVectorial' f as bs = forced (zipWithVectorial f as bs)

-- | Zip three structures by a function, position by position.
--
-- >>> zipWith3Vectorial (\a b c -> a + b * c) (1 :+ 2) (3 :+ 4) (5 :+ 6)
-- 16 :+ 26
zipWith3Vectorial
  :: Vectorial f => (a -> b -> c -> d) -> f a -> f b -> f c -> f d
zipWith3Vectorial f as bs cs = cotraverse zipped
  (Par1 (Left <$> as) :*: Par1 (Right . Left <$> bs)
    :*: Par1 (Right . Right <$> cs))
  where
    -- positions agree, as shapes do
    zipped = \case
      Par1 (Left a) :*: Par1 (Right (Left b)) :*: Par1 (Right (Right c)) ->
        f a b c
      _ -> error "zipWith3Vectorial: positions disagree"

-- | `zipWith3Vectorial`, evaluating every result, left to right.
zipWith3Vectorial'
  :: Vectorial f => (a -> b -> c -> d) -> f a -> f b -> f c -> f d
zipWith3Vectorial' f as bs cs = forced (zipWith3Vectorial f as bs cs)

-- | Unzip a structure of pairs.
--
-- >>> unzipVectorial ((1,'a') :+ (2,'b'))
-- (1 :+ 2,'a' :+ 'b')
unzipVectorial :: Vectorial f => f (a, b) -> (f a, f b)
unzipVectorial abs' = (fst <$> abs', snd <$> abs')

{- | Transpose nested structures, which, as their shapes are the same,
never fails.

>>> transposeVectorial ((1 :+ 2) :+ (3 :+ 4))
(1 :+ 3) :+ (2 :+ 4)
-}
transposeVectorial :: (Vectorial f, Vectorial g) => f (g a) -> g (f a)
transposeVectorial = distribute

{- | A structure of a list's values, when it has exactly as many as
the structure has positions.

>>> fromListVectorial "ab" :: Maybe (Complex Char)
Just ('a' :+ 'b')
>>> fromListVectorial "abc" :: Maybe (Complex Char)
Nothing
-}
fromListVectorial :: forall f a. Vectorial f => [a] -> Maybe (f a)
fromListVectorial as = case mapAccumL fill as (replicateVectorial @f ()) of
  ([], filled) -> sequenceA filled
  _ -> Nothing
  where
    fill (x : xs) () = (xs, Just x)
    fill [] () = ([], Nothing)

-- | The value at a position, if there is one.
--
-- >>> indexVectorial 1 ('a' :+ 'b')
-- Just 'b'
indexVectorial :: Vectorial f => Natural -> f a -> Maybe a
indexVectorial i = listToMaybe . genericDrop i . toList

-- | Adjust the value at a position.
--
-- >>> adjustVectorial 0 negate (1 :+ 2)
-- (-1) :+ 2
adjustVectorial :: Vectorial f => Natural -> (a -> a) -> f a -> f a
adjustVectorial i f = zipWithVectorial
  (\j a -> if i == j then f a else a) positionsVectorial

-- | The zero vector.
zeroVectorial :: (Vectorial f, Num a) => f a
zeroVectorial = replicateVectorial 0

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

-- | A structure, with every value evaluated, left to right.
forced :: Foldable f => f a -> f a
forced xs = foldr seq xs xs
