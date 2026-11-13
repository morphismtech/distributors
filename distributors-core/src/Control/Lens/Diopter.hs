{- |
Module      : Control.Lens.Diopter
Description : diopters
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Control.Lens.Diopter
  ( -- * Diopter
    Diopter
  , ADiopter
  , Dioptrice (..), runDioptrice
    -- * Combinators
  , diopter
  , withDiopter
  , cloneDiopter
  , mapDiopter
  , optioned
  , manied
  , homogenized
  , zipDiopter
  , zipWithDiopter
  , transposeDiopter
  ) where

import Control.Applicative (Alternative)
import Control.Lens
import Control.Lens.Internal.Profunctor
import Data.Profunctor.Distributor
import Data.Profunctor.Monoidal.Cocartesian
import Data.Traversable.Homogeneous
import Data.Void
import GHC.Generics

{- | `Diopter`s are an optic that generalizes
`Control.Lens.Monocle.Monocle`s, of products,
& `Control.Lens.Comonocle.Comonocle`s, of sums,
to countable sums of countable products.
`Control.Lens.Monocle.Monocle` ∪ `Control.Lens.Comonocle.Comonocle`
⊂ `Diopter` ⊂
`Control.Lens.Traversal.Traversal` ∩ `Control.Lens.Prismoid.Prismoid`.

`Diopter`s are isomorphic to t'Dioptrice's, whose shapes are `Homogeneous`,
so these inclusions mirror those of the optics' shapes,

(`Traversable` ∩ `Data.Distributive.Distributive`)
∪ `Data.Traversable.Homogeneous.Enumerable.Enumerable`
⊂ `Homogeneous`.
-}
type Diopter s t a b = forall p f.
  (Distributor p, Applicative f)
    => p a (f b) -> p s (f t)

{- | `ADiopter` is monomorphically a `Diopter`.

> prop> Diopter s t a b ⊂ ADiopter s t a b
-}
type ADiopter s t a b =
  Dioptrice a b a (Identity b) -> Dioptrice a b s (Identity t)

{- | Build a `Diopter`. -}
diopter :: Homogeneous h => (s -> h a) -> (h b -> t) -> Diopter s t a b
diopter f g = unwrapPafb . runDioptrice (Dioptrice f g) . WrapPafb

{- | Convert `ADiopter` to the pair of functions that characterize it. -}
withDiopter
  :: ADiopter s t a b
  -> (forall h. Homogeneous h => (s -> h a) -> (h b -> t) -> r)
  -> r
withDiopter dio k = case runIdentity <$> dio (Identity <$> Dioptrice Par1 unPar1) of
  Dioptrice f g -> k f g

{- | Action of `ADiopter` on `Distributor`s. -}
mapDiopter :: Distributor p => ADiopter s t a b -> p a b -> p s t
mapDiopter dio = withDiopter dio $ \f g -> dimap f g . homogeneously

{- | Clone `ADiopter` so that you can reuse the same
monomorphically typed `Diopter` for different purposes.
-}
cloneDiopter :: ADiopter s t a b -> Diopter s t a b
cloneDiopter dio = withDiopter dio diopter

{- | One or none. -}
optioned :: Diopter (Maybe a) (Maybe b) a b
optioned = unwrapPafb . optionalP . WrapPafb

{- | Zero or more. -}
manied :: Diopter [a] [b] a b
manied = unwrapPafb . manyP . WrapPafb

{- | Build a `Diopter` from a `Homogeneous`
countable sum of countable products.

> prop> traverse = homogenized
> prop> homogenized = ditraversed
-}
homogenized :: Homogeneous t => Diopter (t a) (t b) a b
homogenized = unwrapPafb . homogeneously . WrapPafb

{- | Zip sources of `ADiopter` in the positions of a `Traversable`,
when they have the same shape, or else `Control.Applicative.empty`.

>>> zipDiopter manied (Just . sum) [[1, 2], [3, 4], [5, 6 :: Int]]
Just [9,12]
>>> zipDiopter manied (Just . sum) [[1, 2], [3 :: Int]]
Nothing
-}
zipDiopter
  :: (Traversable f, Alternative g)
  => ADiopter s t a b -> (f a -> g b) -> f s -> g t
zipDiopter dio f = withDiopter dio $ \split merge ->
  fmap merge . zipHomogeneous f . fmap split

{- | Zip two sources of `ADiopter`, when they have the same shape.

>>> zipWithDiopter optioned (+) (Just 1) (Just 2 :: Maybe Int)
Just (Just 3)
>>> zipWithDiopter optioned (+) (Just 1) (Nothing :: Maybe Int)
Nothing
-}
zipWithDiopter :: ADiopter s t a b -> (a -> a -> b) -> s -> s -> Maybe t
zipWithDiopter dio f s0 s1 =
  zipDiopter dio (\(Par1 a0 :*: Par1 a1) -> Just (f a0 a1)) (Par1 s0 :*: Par1 s1)

{- | Transpose sources of `ADiopter` in the positions of a `Traversable`,
when they have the same shape.

>>> transposeDiopter manied [[1, 2, 3], [4, 5, 6 :: Int]]
Just [[1,4],[2,5],[3,6]]
-}
transposeDiopter :: Traversable f => ADiopter s t a (f a) -> f s -> Maybe t
transposeDiopter dio = zipDiopter dio Just

{- | A t'Dioptrice' provides efficient access
to some pair of functions that make up a `Diopter`.
-}
data Dioptrice a b s t where
  Dioptrice
    :: Homogeneous h
    => (s -> h a)
    -> (h b -> t)
    -> Dioptrice a b s t
instance Profunctor (Dioptrice a b) where
  dimap f g (Dioptrice sa bt) = Dioptrice (sa . f) (g . bt)
instance Functor (Dioptrice a b s) where fmap = rmap
instance Applicative (Dioptrice a b s) where
  pure t = Dioptrice (const U1) (const t)
  Dioptrice fx gx <*> Dioptrice fy gy = Dioptrice
    (\s -> fx s :*: fy s)
    (\(h :*: g) -> gx h (gy g))
instance CocartesianMonoidal (Dioptrice a b) where
  zeroP = Dioptrice absurd ridiculous
    where
      ridiculous :: V1 b -> x
      ridiculous = (\case)
  Dioptrice fx gx >+< Dioptrice fy gy = Dioptrice
    (either (L1 . fx) (R1 . fy))
    (\case {L1 h -> Left (gx h); R1 j -> Right (gy j)})
instance Distributor (Dioptrice a b) where
  optionalP (Dioptrice f g) = Dioptrice
    (Comp1 . fmap f)
    (fmap g . unComp1)
  manyP (Dioptrice f g) = Dioptrice
    (Comp1 . fmap f)
    (fmap g . unComp1)

{- | Run a t'Dioptrice' on a `Distributor`. -}
runDioptrice
  :: Distributor p
  => Dioptrice a b s t
  -> p a b -> p s t
runDioptrice (Dioptrice f g) = dimap f g . homogeneously
