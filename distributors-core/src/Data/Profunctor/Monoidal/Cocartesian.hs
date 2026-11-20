{-|
Module      : Data.Profunctor.Monoidal.Cocartesian
Description : cocartesian monoidal profunctors
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Data.Profunctor.Monoidal.Cocartesian
  ( -- * CocartesianMonoidal
    CocartesianMonoidal (..)
  , dialt
    -- * CocartesianChoice
  , CocartesianChoice (..)
  ) where


import Control.Applicative hiding (WrappedArrow)
import Control.Applicative qualified as Ap (WrappedArrow)
import Control.Arrow
import Control.Lens hiding (chosen)
import Control.Lens.Internal.Profunctor
import Control.Lens.PartialIso
import Data.Bifunctor.Clown
import Data.Bifunctor.Joker
import Data.Bifunctor.Product
import Data.Functor.Adjunction
import Data.Functor.Contravariant.Divisible
import Data.Monoid.Disjunctive
import Data.Profunctor hiding (WrappedArrow)
import Data.Profunctor qualified as Pro (WrappedArrow)
import Data.Profunctor.Cayley
import Data.Profunctor.Composition
import Data.Profunctor.Monad
import Data.Profunctor.Yoneda
import Data.Void

-- $setup
-- >>> import Data.Profunctor (dimap)
-- >>> import Data.Void (absurd)

-- CocartesianMonoidal --

{- | A lax `CocartesianMonoidal` sum `Profunctor` has zero `zeroP`
and sum `>+<` lax monoidal structure morphisms,
respecting the cocartesian monoidal structure of `Void` & `Either`,
as `Data.Profunctor.Monoidal.Monoidal` respects that of @()@ & @(,)@.

Laws:

>>> let lunit = dimap (either absurd id) Right
>>> let runit = dimap (either id absurd) Left
>>> :{
let assoc = dimap
      (either (Left . Left) (either (Left . Right) Right))
      (either (either Left (Right . Left)) (Right . Right))
:}

> prop> zeroP >+< p = lunit p
> prop> p >+< zeroP = runit p
> prop> p >+< q >+< r = assoc ((p >+< q) >+< r)
> prop> dimap (f >+< g) (h >+< i) (p >+< q) = dimap f h p >+< dimap g i q
-}
class Profunctor p => CocartesianMonoidal p where

  {- | The zero structure morphism of a `CocartesianMonoidal`.

  `zeroP` has a default for `CocartesianChoice`s.

  > prop> zeroP = falseP
  -}
  zeroP :: p Void Void
  default zeroP :: CocartesianChoice p => p Void Void
  zeroP = falseP

  {- | The sum structure morphism of a `CocartesianMonoidal`.

  `>+<` has a default for `CocartesianChoice`s.

  > prop> x >+< y = alternate (Left x) >|< alternate (Right y)
  -}
  (>+<) :: p a b -> p c d -> p (Either a c) (Either b d)
  default (>+<)
    :: CocartesianChoice p
    => p a b -> p c d -> p (Either a c) (Either b d)
  x >+< y = alternate (Left x) >|< alternate (Right y)
  infixr 3 >+<

instance CocartesianMonoidal (->) where
  zeroP = id
  (>+<) = (+++)
instance CocartesianMonoidal (Forget s) where
  zeroP = Forget absurd
  Forget kL >+< Forget kR = Forget (either kL kR)
instance Decidable f => CocartesianMonoidal (Clown f) where
  zeroP = Clown lost
  Clown x >+< Clown y = Clown (chosen x y)
instance Alternative f => CocartesianMonoidal (Joker f) where
  zeroP = Joker empty
  Joker x >+< Joker y = Joker (Left <$> x <|> Right <$> y)
instance (CocartesianMonoidal p, Functor f)
  => CocartesianMonoidal (WrappedPafb f p) where
    zeroP = WrapPafb (rmap absurd zeroP)
    WrapPafb x >+< WrapPafb y = WrapPafb $
      dialt id (fmap Left) (fmap Right) x y
instance Functor f => CocartesianMonoidal (Star f) where
  zeroP = Star absurd
  Star f >+< Star g =
    Star (either (fmap Left . f) (fmap Right . g))
deriving via (Star m) instance Monad m => CocartesianMonoidal (Kleisli m)
instance Adjunction f u => CocartesianMonoidal (Costar f) where
  zeroP = Costar unabsurdL
  Costar f >+< Costar g = Costar (bimap f g . cozipL)
instance (Applicative f, CocartesianMonoidal p)
  => CocartesianMonoidal (Cayley f p) where
    zeroP = Cayley (pure zeroP)
    Cayley x >+< Cayley y = Cayley ((>+<) <$> x <*> y)
instance (ArrowZero p, ArrowChoice p)
  => CocartesianMonoidal (Pro.WrappedArrow p) where
    zeroP = zeroArrow
    (>+<) = (+++)
deriving via (Pro.WrappedArrow p)
  instance (ArrowZero p, ArrowChoice p)
    => CocartesianMonoidal (Ap.WrappedArrow p)
instance (CocartesianMonoidal p, CocartesianMonoidal q)
  => CocartesianMonoidal (Procompose p q) where
    zeroP = Procompose zeroP zeroP
    Procompose xL yL >+< Procompose xR yR =
      Procompose (xL >+< xR) (yL >+< yR)
instance (CocartesianMonoidal p, CocartesianMonoidal q)
  => CocartesianMonoidal (Product p q) where
    zeroP = Pair zeroP zeroP
    Pair x0 y0 >+< Pair x1 y1 = Pair (x0 >+< x1) (y0 >+< y1)
instance CocartesianMonoidal p => CocartesianMonoidal (Yoneda p) where
  zeroP = proreturn zeroP
  ab >+< cd = proreturn (proextract ab >+< proextract cd)
instance CocartesianMonoidal p => CocartesianMonoidal (Coyoneda p) where
  zeroP = proreturn zeroP
  ab >+< cd = proreturn (proextract ab >+< proextract cd)

{- | `dialt` is a functionalized form of `>+<`. -}
dialt
  :: CocartesianMonoidal p
  => (s -> Either a c)
  -> (b -> t)
  -> (d -> t)
  -> p a b -> p c d -> p s t
dialt f g h p q = dimap f (either g h) (p >+< q)

-- CocartesianChoice --

{- | `CocartesianChoice` co-extends `Choice` and `CocartesianMonoidal`,
with `DisjunctiveMonoid` failure `falseP` and choice `>|<`,
like `Alternative` but without requiring
`Data.Profunctor.Monoidal.Monoidal` structure,
and the `alternate` method, which is a lax monoidal structure morphism
on sums, with these laws relating them.

> prop> left' = alternate . Left
> prop> right' = alternate . Right
> prop> zeroP = falseP
> prop> x >+< y = alternate (Left x) >|< alternate (Right y)

Since @alternate (Left x)@ is parametric in the other summand,
it can't pass that summand through, so by these laws,
`left'` & `right'` of a `CocartesianChoice` never pass the other
summand through, unlike those of @(->)@, which isn't one;
they fail on it, or ignore their input, as those of t'Joker' do.
So a `Control.Lens.Prism.Prism` applied by `Control.Lens.PartialIso.>?`
doesn't pass a mismatch through, either.

For the case of `Functor`s, the analog of `alternate` can be defined
without any other constraint, but the case of `Profunctor`s turns
out to be slightly more complex, necessitating `CocartesianChoice`.

>>> :{
alternateF :: Functor f => Either (f a) (f b) -> f (Either a b)
alternateF = either (fmap Left) (fmap Right)
:}
-}
class (CocartesianMonoidal p, Choice p, forall x y. DisjunctiveMonoid (p x y))
  => CocartesianChoice p where

  {- | The structure morphism for a `CocartesianChoice`,
  `alternate` has a default for `Choice` & `Cochoice` partial distributors.
  -}
  alternate
    :: Either (p a b) (p c d)
    -> p (Either a c) (Either b d)
  default alternate
    :: Cochoice p
    => Either (p a b) (p c d)
    -> p (Either a c) (Either b d)
  alternate =
    dimapMaybe (either Just (pure Nothing)) (Just . Left)
    |||
    dimapMaybe (either (pure Nothing) Just) (Just . Right)

instance (CocartesianChoice p, Applicative f)
  => CocartesianChoice (WrappedPafb f p) where
    alternate =
      let
        f = WrapPafb
          . rmap (either (fmap Left) pure)
          . alternate
          . Left
          . unwrapPafb
        g = WrapPafb
          . rmap (either pure (fmap Right))
          . alternate
          . Right
          . unwrapPafb
      in
        either f g
instance CocartesianChoice p => CocartesianChoice (Coyoneda p) where
  alternate (Left p) = proreturn (alternate (Left (proextract p)))
  alternate (Right p) = proreturn (alternate (Right (proextract p)))
instance CocartesianChoice p => CocartesianChoice (Yoneda p) where
  alternate (Left p) = proreturn (alternate (Left (proextract p)))
  alternate (Right p) = proreturn (alternate (Right (proextract p)))
instance Alternative f => CocartesianChoice (Joker f) where
  alternate (Left (Joker x)) = Joker (Left <$> x)
  alternate (Right (Joker y)) = Joker (Right <$> y)
