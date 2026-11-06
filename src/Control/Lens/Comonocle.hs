{- |
Module      : Control.Lens.Comonocle
Description : comonocles
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable

`Comonocle`s are to `CocartesianMonoidal` `Profunctor`s,
as `Control.Lens.Monocle.Monocle`s are to
`Data.Profunctor.Monoidal.Monoidal` `Profunctor`s.

See Clarke, Elkins, Gibbons, Loregian, Milewski, Pillmore & Román,
[Profunctor Optics, a Categorical Update](https://arxiv.org/abs/2001.07488)
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
  , enumerated
  , cased
  , enumed
    -- * Comonocular
  , Comonocular (..)
  , runComonocular
  ) where

import Control.Lens
import Control.Lens.Internal.Profunctor
import Data.Profunctor.Monoidal.Cocartesian
import Data.Traversable.Homogeneous
import Data.Void
import GHC.Generics

{- | `Comonocle`s are an optic for homogeneous sums,
@s ≅ (e, a)@ & @t ≅ (e, b)@ for some enumerable tag type @e@.

Since @(->)@ is `CocartesianMonoidal`,
every `Comonocle` is a `Control.Lens.Lens.Lens`,
one whose complement is enumerable.

>>> view cased (GT, 'x')
'x'
>>> over cased succ (EQ, 'a')
(EQ,'b')

Since every `Data.Profunctor.Distributor.Distributor`
is `CocartesianMonoidal`, every `Comonocle` is
a `Control.Lens.Diopter.Diopter`.

Every `Control.Lens.Iso.Iso` is a `Comonocle`.

`Comonocle`s are isomorphic to `Comonocular`s.
-}
type Comonocle s t a b = forall p f.
  (CocartesianMonoidal p, Functor f)
    => p a (f b) -> p s (f t)

{- | `AComonocle` is monomorphically a `Comonocle`. -}
type AComonocle s t a b =
  Comonocular a b a (Identity b) -> Comonocular a b s (Identity t)

{- | Build a `Comonocle` from an `Enumerable` decomposition. -}
comonocle :: Enumerable h => (s -> h a) -> (h b -> t) -> Comonocle s t a b
comonocle f g = unwrapPafb . runComonocular (Comonocular f g) . WrapPafb

{- | Convert `AComonocle` to the pair of functions that characterize it. -}
withComonocle
  :: AComonocle s t a b
  -> (forall h. Enumerable h => (s -> h a) -> (h b -> t) -> r)
  -> r
withComonocle com k =
  case runIdentity <$> com (Identity <$> Comonocular Par1 unPar1) of
    Comonocular f g -> k f g

{- | Clone `AComonocle` so that you can reuse the same
monomorphically typed `Comonocle` for different purposes.
-}
cloneComonocle :: AComonocle s t a b -> Comonocle s t a b
cloneComonocle com = withComonocle com comonocle

{- | Action of `AComonocle` on `CocartesianMonoidal` `Profunctor`s. -}
mapComonocle
  :: CocartesianMonoidal p
  => AComonocle s t a b -> p a b -> p s t
mapComonocle com = withComonocle com $ \f g -> dimap f g . enumerately

{- | Build a `Comonocle` from an `Enumerable` homogeneous sum.

prop> enumerated = comonocle id id
-}
enumerated :: Enumerable h => Comonocle (h a) (h b) a b
enumerated = unwrapPafb . enumerately . WrapPafb

{- | A `Comonocle` onto the value tagged by a `Bounded` `Enum`.

prop> cased = enumerated
-}
cased :: (Enum e, Bounded e) => Comonocle (e, a) (e, b) a b
cased = enumerated

{- | A `Bounded` `Enum` is a homogeneous sum of units.

prop> mapComonocle enumed = enumP . const
-}
enumed :: (Enum e, Bounded e) => Comonocle e e () ()
enumed = dimap (,()) (fmap fst) . cased

{- | `Comonocular` provides efficient access
to the pair of functions that make up a `Comonocle`.
It is the free `CocartesianMonoidal` on a single @p a b@.
-}
data Comonocular a b s t where
  Comonocular
    :: Enumerable h
    => (s -> h a)
    -> (h b -> t)
    -> Comonocular a b s t
instance Profunctor (Comonocular a b) where
  dimap f g (Comonocular sa bt) = Comonocular (sa . f) (g . bt)
instance Functor (Comonocular a b s) where fmap = rmap
instance CocartesianMonoidal (Comonocular a b) where
  zeroP = Comonocular absurd ridiculous
    where
      ridiculous :: V1 b -> x
      ridiculous = (\case)
  Comonocular fx gx >+< Comonocular fy gy = Comonocular
    (either (L1 . fx) (R1 . fy))
    (\case {L1 h -> Left (gx h); R1 j -> Right (gy j)})

{- | Run a `Comonocular` on a `CocartesianMonoidal`. -}
runComonocular
  :: CocartesianMonoidal p
  => Comonocular a b s t
  -> p a b -> p s t
runComonocular (Comonocular f g) = dimap f g . enumerately
