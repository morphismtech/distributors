{- |
Module      : Control.Lens.Monocle
Description : monocles
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable

See Oliveira, Jaskelioff & de Melo,
[On Structuring Functional Programs with Monoidal Profunctors](https://arxiv.org/abs/2207.00852)
-}

module Control.Lens.Monocle
  ( -- * Monocle
    Monocle
  , AMonocle
    -- * Combinators
  , monocle
  , withMonocle
  , cloneMonocle
  , imprism
  , mapMonocle
  , crossMonocle
  , ditraversed
  , forevered
    -- * Monocular
  , Monocular (..), runMonocular
    -- * Comonocle
  , Comonocle
  , AComonocle
  , comonocle
  , withComonocle
  , cloneComonocle
  , mapComonocle
  , altComonocle
  , crossComonocle
  , indexComonocle
  , zipWithComonocle
  , enumerated
    -- * Comonocular
  , Comonocular (..), runComonocular
  ) where

import Control.Lens hiding (Traversing)
import Control.Lens.Internal.Profunctor
import Data.Distributive
import Data.Functor.Compose
import Data.Profunctor.Monoidal
import Data.Profunctor.Monoidal.Cocartesian
import Data.Traversable.Homogeneous
import Data.Void (Void, absurd)
import GHC.Generics (Par1 (..), V1, (:+:) (..))
import Numeric.Natural (Natural)

-- $setup
-- >>> import Data.Complex

{- | `Monocle`s are an optic that generalizes
`Control.Lens.Traversal.Traversal`s & `Control.Lens.Grate.Grate`s.

Every `Control.Lens.Iso.Iso` is a `Monocle`.

`Monocle`s are isomorphic to `Monocular`s.
-}
type Monocle s t a b = forall p f.
  (Monoidal p, Applicative f)
    => p a (f b) -> p s (f t)

{- | `AMonocle` is monomorphically a `Monocle`. -}
type AMonocle s t a b =
  Monocular a b a (Identity b) -> Monocular a b s (Identity t)

{- | Build a `Monocle` from a concrete `Monocular`. -}
monocle :: Monocular a b s t -> Monocle s t a b
monocle mon = unwrapPafb . runMonocular mon . WrapPafb

{- | Action of `AMonocle` on `Monoidal` `Profunctor`s. -}
mapMonocle :: Monoidal p => AMonocle s t a b -> p a b -> p s t
mapMonocle mon p = withMonocle mon $ \f -> lmap f p

{- | Clone `AMonocle` so that you can reuse the same
monomorphically typed `Monocle` for different purposes.
-}
cloneMonocle :: AMonocle s t a b -> Monocle s t a b
cloneMonocle mon = unwrapPafb . mapMonocle mon . WrapPafb

{- | Convert a `Monocle` to an improper `Control.Lens.Prism.Prism`.

>>> review (imprism ditraversed) 1 :: Complex Int
1 :+ 1
>>> preview (imprism ditraversed) (1 :+ 2 :: Complex Int)
Just 1
-}
imprism :: Monocle s t a b -> Prism s t a b
imprism mon = clonePrism mon

{- | Construct a `Monocle` on pairs from components, with the same foci,
since products of powers add, \(a^m \times a^n = a^{m+n}\),
as `Control.Lens.Traversal.beside` does `Control.Lens.Traversal.Traversal`s.

>>> over (crossMonocle id ditraversed) negate (1, 2 :+ 3)
(-1,(-2) :+ (-3))
-}
crossMonocle
  :: AMonocle s t a b
  -> AMonocle u v a b
  -> Monocle (s,u) (t,v) a b
crossMonocle x y p =
  rmap (uncurry (liftA2 (,))) (cloneMonocle x p >*< cloneMonocle y p)

{- | Build a `Monocle` from a `Traversable` & `Distributive`,
homogeneous, countable product.

@prop> traverse = ditraversed@
@prop> cotraversed = ditraversed@
-}
ditraversed :: (Traversable g, Distributive g) => Monocle (g a) (g b) a b
ditraversed = unwrapPafb . ditraverse . WrapPafb

{- | Repeat action indefinitely. -}
forevered :: Monocle s t () b
forevered = unwrapPafb . foreverP . WrapPafb

{- | Run `AMonocle` over an `Applicative`. -}
withMonocle :: Applicative f => AMonocle s t a b -> ((s -> a) -> f b) -> f t
withMonocle mon = unMonocular (runIdentity <$> mon (Identity <$> Monocular ($ id)))

{- | `Monocular` provides an efficient
concrete representation of `Monocle`s. -}
newtype Monocular a b s t = Monocular
  {unMonocular :: forall f. Applicative f => ((s -> a) -> f b) -> f t}
instance Profunctor (Monocular a b) where
  dimap f g (Monocular k) =
    Monocular (fmap g . k . (. (. f)))
instance Functor (Monocular a b s) where fmap = rmap
instance Applicative (Monocular a b s) where
  pure t = Monocular (pure (pure t))
  Monocular x <*> Monocular y = Monocular (liftA2 (<*>) x y)

{- | Run a `Monocular` on a `Monoidal` `Profunctor`. -}
runMonocular :: Monoidal p => Monocular a b s t -> p a b -> p s t
runMonocular (Monocular k) p = k $ \f -> lmap f p

{- | `Comonocle`s are an optic dual to `Monocle`s, by sums,
which focus on the one copy that an `Enumerable` sum holds.

Every `Control.Lens.Iso.Iso` is a `Comonocle`,
& every `Comonocle` is a `Control.Lens.Lens.Lens`,
whose residue is which copy is held.

>>> view enumerated (Identity 'a')
'a'

`Comonocle`s are isomorphic to `Comonocular`s.
-}
type Comonocle s t a b = forall p f.
  (CocartesianMonoidal p, Functor f)
    => p a (f b) -> p s (f t)

{- | `AComonocle` is monomorphically a `Comonocle`. -}
type AComonocle s t a b =
  Comonocular a b a (Identity b) -> Comonocular a b s (Identity t)

{- | Build a `Comonocle` from a concrete `Comonocular`. -}
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

>>> set (altComonocle id enumerated) 'x' (Right (Identity 'y'))
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

>>> over (crossComonocle enumerated id) (\(a, c) -> (a + c, show c)) (Identity 1, 2)
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
      (\(Compose bds) -> (f (fmap (fst . extractEnumerable) bds), h (fmap snd (extractEnumerable bds))))

{- | The `Control.Lens.Indexed.IndexedLens` of `AComonocle`,
indexed by which copy is held, numbered from 0, left to right.
Numbering diverges past a summand of infinitely many copies.

>>> iview (indexComonocle (altComonocle id id)) (Right 'a' :: Either Char Char)
(1,'a')
-}
indexComonocle :: AComonocle s t a b -> IndexedLens Natural s t a b
indexComonocle mon = withComonocle mon $ \split merge ->
  ilens (\s -> let as = split s in (indexEnumerable as, extractEnumerable as))
    (\s b -> merge (b <$ split s))

{- | Zip two sources of `AComonocle`, when they hold the same copy,
dual to `Control.Lens.Grate.cotraverseOf`, which zips every `Monocle`.

>>> zipWithComonocle (altComonocle id id) (+) (Left 1) (Left 2 :: Either Int Int)
Just (Left 3)
>>> zipWithComonocle (altComonocle id id) (+) (Left 1) (Right 2 :: Either Int Int)
Nothing
-}
zipWithComonocle
  :: AComonocle s t a b -> (a -> a -> b) -> s -> s -> Maybe t
zipWithComonocle mon f =
  runZipping (mapComonocle mon (Zipping (\a0 a1 -> Just (f a0 a1))))

{- | The `Comonocle` of an `Enumerable` sum's copy.

>>> over enumerated (+ 1) (Identity 1)
Identity 2
-}
enumerated :: Enumerable f => Comonocle (f a) (f b) a b
enumerated = unwrapPafb . enumerably . WrapPafb

{- | `Comonocular` provides a concrete representation of `Comonocle`s,
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

{- | Run a `Comonocular` on a `CocartesianMonoidal` `Profunctor`. -}
runComonocular
  :: CocartesianMonoidal p => Comonocular a b s t -> p a b -> p s t
runComonocular (Comonocular split merge) = dimap split merge . enumerably
