{- |
Module      : Control.Lens.Comonocle
Description : comonocles
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Control.Lens.Comonocle
  ( -- * Comonocle
    Comonocle
  , AComonocle
    -- * Combinators
  , comonocle
  , withComonocle
  , cloneComonocle
  , mapComonocle
  , altComonocle
  , crossComonocle
  , indexComonocle
  , countComonocle
  , fromComonocle
  , succComonocle
  , predComonocle
  , enumerateComonocle
  , enumerateFromThenComonocle
  , enumerateFromToComonocle
  , enumerateFromThenToComonocle
  , zipComonocle
  , zipWithComonocle
  , _Enumerable
  , _BoundedEnum
    -- * Comonocular
  , Comonocular (..), runComonocular
  ) where

import Control.Applicative (Alternative)
import Control.Lens hiding (Traversing)
import Control.Lens.PartialIso
import Control.Lens.Internal.Profunctor
import Data.Functor.Compose
import Data.Profunctor.Monoidal
import Data.Profunctor.Monoidal.Cocartesian
import Data.Traversable.Homogeneous
import Data.Traversable.Homogeneous.Enumerable
import Data.Void (Void, absurd)
import GHC.Generics (Par1 (..), V1, (:+:) (..), (:*:) (..))
import Numeric.Natural (Natural)

-- $setup
-- >>> import Control.Lens
-- >>> import Control.Lens.PartialIso (withPartialIso)
-- >>> import Data.Functor.Identity

{- | `Comonocle`s are an optic dual to `Control.Lens.Monocle.Monocle`s, by sums,
which focus on the one copy that an `Enumerable` sum holds.

Every `Control.Lens.Iso.Iso` is a `Comonocle`,
& every `Comonocle` is a `Control.Lens.Lens.Lens`,
whose residue is which copy is held.

>>> view _Enumerable (Identity 'a')
'a'

`Comonocle`s are isomorphic to t'Comonocular's.
-}
type Comonocle s t a b = forall p f.
  (CocartesianMonoidal p, Functor f)
    => p a (f b) -> p s (f t)

{- | `AComonocle` is monomorphically a `Comonocle`. -}
type AComonocle s t a b =
  Comonocular a b a (Identity b) -> Comonocular a b s (Identity t)

{- | Build a `Comonocle` from a concrete t'Comonocular'. -}
comonocle :: Comonocular a b s t -> Comonocle s t a b
comonocle mon = unwrapPafb . runComonocular mon . WrapPafb

{- | Convert `AComonocle` to the pair of functions that characterize it. -}
withComonocle
  :: AComonocle s t a b
  -> (forall f. Enumerable f => (s -> f a) -> (f b -> t) -> r)
  -> r
withComonocle mon k =
  case rmap runIdentity (mon (rmap Identity (Comonocular Par1 unPar1))) of
    Comonocular split merge -> k split merge

{- | Clone `AComonocle` so that you can reuse the same
monomorphically typed `Comonocle` for different purposes.
-}
cloneComonocle :: AComonocle s t a b -> Comonocle s t a b
cloneComonocle mon = withComonocle mon $ \split merge ->
  comonocle (Comonocular split merge)

{- | Action of `AComonocle` on `CocartesianMonoidal` `Profunctor`s. -}
mapComonocle
  :: CocartesianMonoidal p => AComonocle s t a b -> p a b -> p s t
mapComonocle mon = withComonocle mon $ \split merge ->
  dimap split merge . enumerably

{- | Construct a `Comonocle` on `Either`s from components, with the same foci,
since sums of copies add, \(m a + n a = (m+n) a\),
as `Control.Lens.Lens.choosing` does `Control.Lens.Lens.Lens`es.

>>> set (altComonocle id _Enumerable) 'x' (Right (Identity 'y'))
Right (Identity 'x')
-}
altComonocle
  :: AComonocle s t a b
  -> AComonocle u v a b
  -> Comonocle (Either s u) (Either t v) a b
altComonocle x y p = rmap (either (fmap Left) (fmap Right))
  (cloneComonocle x p >+< cloneComonocle y p)

{- | Construct a `Comonocle` on pairs from components,
since products of sums of copies distribute,
\(m a \times n c = (m n) (a \times c)\).

>>> over (crossComonocle _Enumerable id) (\(a, c) -> (a + c, show c)) (Identity 1, 2)
(Identity 3,"2")
-}
crossComonocle
  :: AComonocle s t a b
  -> AComonocle u v c d
  -> Comonocle (s,u) (t,v) (a,c) (b,d)
crossComonocle x y =
  withComonocle x $ \e f ->
  withComonocle y $ \g h ->
    comonocle $ Comonocular
      (\(s,u) -> Compose (fmap (\a -> fmap (a,) (g u)) (e s)))
      (\(Compose i) -> f >*< h $
          let
            (_, j) = review fromEnumerable i
            k = fmap (review fromEnumerable) i
          in
            (fmap (fst . snd) k, fmap snd j)
      )

{- | The `Control.Lens.Indexed.IndexedLens` of `AComonocle`,
indexed by which copy is held, numbered from 0, left to right.
Numbering diverges past a summand of infinitely many copies.

>>> iview (indexComonocle (altComonocle id id)) (Right 'a' :: Either Char Char)
(1,'a')
-}
indexComonocle :: AComonocle s t a b -> IndexedLens Natural s t a b
indexComonocle mon = withComonocle mon $ \split merge -> ilens
  (review fromEnumerable . split)
  (\s b -> merge (b <$ split s))

{- | The copy of `AComonocle` at an index, holding a focus, if there is one,
like `toEnum`, & inverse to `indexComonocle`.

>>> preview (fromComonocle _BoundedEnum) (2, ()) :: Maybe Ordering
Just GT
>>> preview (fromComonocle _BoundedEnum) (3, ()) :: Maybe Ordering
Nothing
-}
fromComonocle :: AComonocle s s a a -> Prism' (Natural, a) s
fromComonocle mon = withComonocle mon $ \split merge -> prism'
  (review fromEnumerable . split)
  (fmap merge . preview fromEnumerable)

{- | Zip two sources of `AComonocle`, when they hold the same copy,
dual to `Control.Lens.Grate.cotraverseOf`, which zips every `Monocle`.

>>> zipWithComonocle (altComonocle id id) (+) (Left 1) (Left 2 :: Either Int Int)
Just (Left 3)
>>> zipWithComonocle (altComonocle id id) (+) (Left 1) (Right 2 :: Either Int Int)
Nothing
-}
zipWithComonocle
  :: AComonocle s t a b -> (a -> a -> b) -> s -> s -> Maybe t
zipWithComonocle mon f s0 s1 =
  zipComonocle mon (\(Par1 a0 :*: Par1 a1) -> Just (f a0 a1)) (Par1 s0 :*: Par1 s1)

{- | Zip sources of `AComonocle` in the positions of a `Traversable`,
when they all hold the same copy, or else `Control.Applicative.empty`.

>>> zipComonocle (altComonocle id id) (Just . sum) [Left 1, Left 2, Left 3 :: Either Int Int]
Just (Left 6)
>>> zipComonocle (altComonocle id id) (Just . sum) [Left 1, Right 2 :: Either Int Int]
Nothing
-}
zipComonocle
  :: (Traversable f, Alternative g)
  => AComonocle s t a b -> (f a -> g b) -> f s -> g t
zipComonocle mon f = runZipporah (mapComonocle mon (Zipporah f))

{- | How many copies `AComonocle` has, like the size of a `Bounded` `Enum`.
It diverges for infinitely many copies, & takes time linear in their number.

>>> countComonocle (_BoundedEnum @Ordering)
3
-}
countComonocle :: AComonocle s t a b -> Natural
countComonocle mon = withComonocle mon $ \split _ -> copies split
  where
    copies :: forall f x y. Enumerable f => (x -> f y) -> Natural
    copies _ = case enumerably (pure () :: Enumerator () ()) :: Enumerator (f ()) (f ()) of
      Enumerator count _ _ -> count

{- | The next copy of `AComonocle`, holding the same focus,
if there is one, like `succ`, & conversely, the previous copy, like `pred`.

>>> withPartialIso (succComonocle _BoundedEnum) const EQ
Just GT
>>> withPartialIso (succComonocle _BoundedEnum) const GT
Nothing
-}
succComonocle :: AComonocle s s a a -> PartialIso' s s
succComonocle mon =
  withComonocle mon $ \split merge ->
  withPartialIso succEnumerable $ \hither thither ->
    partialIso 
      (fmap merge . hither . split)
      (fmap merge . thither . split)

{- | The previous copy of `AComonocle`, holding the same focus,
if there is one, like `pred`, & conversely, the next copy, like `succ`.

>>> withPartialIso (predComonocle _BoundedEnum) const EQ
Just LT
>>> withPartialIso (predComonocle _BoundedEnum) const LT
Nothing
-}
predComonocle :: AComonocle s s a a -> PartialIso' s s
predComonocle mon = coPartialIso (succComonocle mon)

{- | The copies of `AComonocle` from one onward, holding the same focus,
like `enumFrom`.

>>> enumerateComonocle _BoundedEnum False
[False,True]
>>> enumerateComonocle (altComonocle id id) (Left 'x' :: Either Char Char)
[Left 'x',Right 'x']
-}
enumerateComonocle :: AComonocle s s a a -> s -> [s]
enumerateComonocle mon s =
  withComonocle mon $ \split merge -> merge <$> enumerateFrom (split s)

{- | The copies of `AComonocle` from one onward, holding its focus,
stepping by the copy of another, like `enumFromThen`.

>>> enumerateFromThenComonocle _BoundedEnum GT EQ
[GT,EQ,LT]
-}
enumerateFromThenComonocle :: AComonocle s s a a -> s -> s -> [s]
enumerateFromThenComonocle mon s s' = withComonocle mon $ \split merge ->
  merge <$> enumerateFromThen (split s) (split s')

{- | The copies of `AComonocle` from one to the copy of another,
holding its focus, like `enumFromTo`.

>>> enumerateFromToComonocle _BoundedEnum LT EQ
[LT,EQ]
-}
enumerateFromToComonocle :: AComonocle s s a a -> s -> s -> [s]
enumerateFromToComonocle mon s s'' = withComonocle mon $ \split merge ->
  merge <$> enumerateFromTo (split s) (split s'')

{- | The copies of `AComonocle` from one to the copy of another,
holding its focus, stepping by the copy of a third, like `enumFromThenTo`.

>>> enumerateFromThenToComonocle _BoundedEnum LT GT LT
[LT]
-}
enumerateFromThenToComonocle :: AComonocle s s a a -> s -> s -> s -> [s]
enumerateFromThenToComonocle mon s s' s'' = withComonocle mon $ \split merge ->
  merge <$> enumerateFromThenTo (split s) (split s') (split s'')

{- | The `Comonocle` of an `Enumerable` sum's copy.

>>> over _Enumerable (+ 1) (Identity 1)
Identity 2
-}
_Enumerable :: Enumerable f => Comonocle (f a) (f b) a b
_Enumerable = unwrapPafb . enumerably . WrapPafb

{- | The `Comonocle` of a `Bounded` `Enum`, as copies of @()@,
numbered by `fromEnum` from `minBound`.

>>> iview (indexComonocle _BoundedEnum) True
(1,())
-}
_BoundedEnum :: (Bounded a, Enum a) => Comonocle a a () ()
_BoundedEnum = iso (\x -> (x,())) (\(x,()) -> x) . _Enumerable

{- | t'Comonocular' provides a concrete representation of `Comonocle`s,
by an `Enumerable` sum of copies.
-}
data Comonocular a b s t where
  Comonocular
    :: Enumerable f
    => (s -> f a)
    -> (f b -> t)
    -> Comonocular a b s t
instance Profunctor (Comonocular a b) where
  dimap f g (Comonocular split merge) = Comonocular (split . f) (g . merge)
instance CocartesianMonoidal (Comonocular a b) where
  zeroP = Comonocular (absurd :: Void -> V1 a) (\case)
  Comonocular split0 merge0 >+< Comonocular split1 merge1 = Comonocular
    (either (L1 . split0) (R1 . split1))
    (\case L1 x -> Left (merge0 x); R1 y -> Right (merge1 y))

{- | Run a t'Comonocular' on a `CocartesianMonoidal` `Profunctor`. -}
runComonocular
  :: CocartesianMonoidal p => Comonocular a b s t -> p a b -> p s t
runComonocular (Comonocular split merge) = dimap split merge . enumerably
