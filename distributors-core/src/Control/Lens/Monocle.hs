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
  , ditraversed
  , forevered
    -- * Monocular
  , Monocular (..), runMonocular
    -- * Comonocle
  , Comonocle
  , Comonocle'
  , comonocle
  , enumerated
  , enumBounded
    -- * Comonocular
  , Comonocular (..), runComonocular
  ) where

import Control.Lens hiding (Traversing)
import Control.Lens.Internal.Profunctor
import Data.Distributive
import Data.List.NonEmpty (NonEmpty (..))
import Data.Profunctor.Monoidal
import Data.Profunctor.Monoidal.Cocartesian
import Data.Traversable.Homogeneous
import Data.Void (Void, absurd)
import GHC.Generics (V1, (:+:) (..))

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

{- | Build a `Monocle` from a `Traversable` & `Distributive`,
homogeneous, countable product.

prop> traverse = ditraversed
prop> cotraversed = ditraversed
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

Every `Control.Lens.Iso.Iso` is a `Comonocle`.

`Comonocle`s are isomorphic to `Comonocular`s.
-}
type Comonocle s t a b = forall p f.
  (CocartesianMonoidal p, Functor f)
    => p a (f b) -> p s (f t)

-- | A simple `Comonocle`.
type Comonocle' s a = Comonocle s s a a

{- | Build a `Comonocle` from a concrete `Comonocular`. -}
comonocle :: Comonocular a b s t -> Comonocle s t a b
comonocle mon = unwrapPafb . runComonocular mon . WrapPafb

{- | The `Comonocle` of an `Enumerable` sum's copy.

>>> over enumerated (+ 1) (Identity 1)
Identity 2
-}
enumerated :: Enumerable f => Comonocle (f a) (f b) a b
enumerated = unwrapPafb . enumerably . WrapPafb

{- | The `Comonocle` of a bounded enumeration, as a sum of its values,
each of which holds nothing.
-}
enumBounded :: (Enum a, Bounded a) => Comonocle' a ()
enumBounded p = values (minBound :| drop 1 [minBound .. maxBound])
  where
    value a = dimap (const ()) (fmap (const a)) p
    values = \case
      a :| [] -> value a
      a :| (b : others) -> dialt
        (\x -> if fromEnum x == fromEnum a then Left x else Right x)
        id
        id
        (value a)
        (values (b :| others))

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
