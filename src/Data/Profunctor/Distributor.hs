{-|
Module      : Data.Profunctor.Distributor
Description : distributors
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Data.Profunctor.Distributor
  ( -- * CocartesianMonoidal
    CocartesianMonoidal (..)
  , dialt
    -- * Distributor
  , Distributor (..)
    -- * CocartesianChoice
  , CocartesianChoice (..)
    -- * Alternator
  , Alternator (..)
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
import Data.Profunctor.Monoidal
import Data.Profunctor.Yoneda
import Data.Void

-- Distributor --

{- | A `Distributor`, or lax distributive profunctor,
respects [distributive category]
(https://ncatlab.org/nlab/show/distributive+category)
structure, that is nilary and binary products and coproducts,
@()@, @(,)@, `Void` and `Either`. It has zero `zeroP`
and sum `>+<` lax monoidal structure morphisms.

In addition to the product laws for `Monoidal`, we have
sum laws for `Distributor`.

Laws:

>>> let lunit = dimap (either absurd id) Right
>>> let runit = dimap (either id absurd) Left
>>> :{
let assoc = dimap
      (either (Left . Left) (either (Left . Right) Right))
      (either (either Left (Right . Left)) (Right . Right))
:}

prop> zeroP >+< p = lunit p
prop> p >+< zeroP = runit p
prop> p >+< q >+< r = assoc ((p >+< q) >+< r)
prop> dimap (f >+< g) (h >+< i) (p >+< q) = dimap f h p >+< dimap g i q

`Distributor` additionally has methods `manyP` & `optionalP`,
distributing an action over @[]@ and `Maybe` datatypes,
which generalize to `Data.Traversable.Homogeneous.homogeneously`
distributing an action over
`Data.Traversable.Homogeneous.Homogeneous`
sum-of-products datatypes.

-}
class Profunctor p => CocartesianMonoidal p where

  {- | The zero structure morphism of a `Distributor`.

  `zeroP` has a default for `CocartesianChoice`s.

  prop> zeroP = falseP
  -}
  zeroP :: p Void Void
  default zeroP :: CocartesianChoice p => p Void Void
  zeroP = falseP

  {- | The sum structure morphism of a `Distributor`.

  `>+<` has a default for `CocartesianChoice`s.

  prop> x >+< y = alternate (Left x) >|< alternate (Right y)
  -}
  (>+<) :: p a b -> p c d -> p (Either a c) (Either b d)
  default (>+<)
    :: CocartesianChoice p
    => p a b -> p c d -> p (Either a c) (Either b d)
  x >+< y = alternate (Left x) >|< alternate (Right y)
  infixr 3 >+<

class (Monoidal p, CocartesianMonoidal p) => Distributor p where

  {- | One or none. -}
  optionalP :: p a b -> p (Maybe a) (Maybe b)
  optionalP p = eotMaybe >~ p >+< oneP

  {- | Zero or more. -}
  manyP :: p a b -> p [a] [b]
  manyP p = eotList >~ p >*< manyP p >+< oneP

instance CocartesianMonoidal (->) where
  zeroP = id
  (>+<) = (+++)
instance Distributor (->)
instance CocartesianMonoidal (Forget s) where
  zeroP = Forget absurd
  Forget kL >+< Forget kR = Forget (either kL kR)
instance Monoid s => Distributor (Forget s)
instance Decidable f => CocartesianMonoidal (Clown f) where
  zeroP = Clown lost
  Clown x >+< Clown y = Clown (chosen x y)
instance Decidable f => Distributor (Clown f)
instance Alternative f => CocartesianMonoidal (Joker f) where
  zeroP = Joker empty
  Joker x >+< Joker y = Joker (Left <$> x <|> Right <$> y)
instance Alternative f => Distributor (Joker f) where
  optionalP (Joker x) = Joker (optional x)
  manyP (Joker x) = Joker (many x)
instance (CocartesianMonoidal p, Applicative f)
  => CocartesianMonoidal (WrappedPafb f p) where
    zeroP = WrapPafb (rmap pure zeroP)
    WrapPafb x >+< WrapPafb y = WrapPafb $
      dialt id (fmap Left) (fmap Right) x y
instance (Distributor p, Applicative f)
  => Distributor (WrappedPafb f p) where
    manyP (WrapPafb x) = WrapPafb (rmap sequenceA (manyP x))
    optionalP (WrapPafb x) = WrapPafb (rmap sequenceA (optionalP x))
instance Functor f => CocartesianMonoidal (Star f) where
  zeroP = Star absurd
  Star f >+< Star g =
    Star (either (fmap Left . f) (fmap Right . g))
instance Applicative f => Distributor (Star f) where
  optionalP (Star f) = Star (traverse f)
  manyP (Star f) = Star (traverse f)
deriving via (Star m) instance Monad m => CocartesianMonoidal (Kleisli m)
deriving via (Star m) instance Monad m => Distributor (Kleisli m)
instance Adjunction f u => CocartesianMonoidal (Costar f) where
  zeroP = Costar unabsurdL
  Costar f >+< Costar g = Costar (bimap f g . cozipL)
instance Adjunction f u => Distributor (Costar f)
instance (Applicative f, CocartesianMonoidal p)
  => CocartesianMonoidal (Cayley f p) where
    zeroP = Cayley (pure zeroP)
    Cayley x >+< Cayley y = Cayley ((>+<) <$> x <*> y)
instance (Applicative f, Distributor p)
  => Distributor (Cayley f p) where
    optionalP (Cayley x) = Cayley (optionalP <$> x)
    manyP (Cayley x) = Cayley (manyP <$> x)
instance (ArrowZero p, ArrowChoice p)
  => CocartesianMonoidal (Pro.WrappedArrow p) where
    zeroP = zeroArrow
    (>+<) = (+++)
instance (ArrowZero p, ArrowChoice p)
  => Distributor (Pro.WrappedArrow p)
deriving via (Pro.WrappedArrow p)
  instance (ArrowZero p, ArrowChoice p)
    => CocartesianMonoidal (Ap.WrappedArrow p)
deriving via (Pro.WrappedArrow p)
  instance (ArrowZero p, ArrowChoice p)
    => Distributor (Ap.WrappedArrow p)
instance (CocartesianMonoidal p, CocartesianMonoidal q)
  => CocartesianMonoidal (Procompose p q) where
    zeroP = Procompose zeroP zeroP
    Procompose xL yL >+< Procompose xR yR =
      Procompose (xL >+< xR) (yL >+< yR)
instance (Distributor p, Distributor q)
  => Distributor (Procompose p q) where
    optionalP (Procompose f g) =
      Procompose (optionalP f) (optionalP g)
    manyP (Procompose f g) =
      Procompose (manyP f) (manyP g)
instance (CocartesianMonoidal p, CocartesianMonoidal q)
  => CocartesianMonoidal (Product p q) where
    zeroP = Pair zeroP zeroP
    Pair x0 y0 >+< Pair x1 y1 = Pair (x0 >+< x1) (y0 >+< y1)
instance (Distributor p, Distributor q)
  => Distributor (Product p q) where
    optionalP (Pair f g) =
      Pair (optionalP f) (optionalP g)
    manyP (Pair f g) =
      Pair (manyP f) (manyP g)
instance CocartesianMonoidal p => CocartesianMonoidal (Yoneda p) where
  zeroP = proreturn zeroP
  ab >+< cd = proreturn (proextract ab >+< proextract cd)
instance Distributor p => Distributor (Yoneda p) where
  optionalP = proreturn . optionalP . proextract
  manyP = proreturn . manyP . proextract
instance CocartesianMonoidal p => CocartesianMonoidal (Coyoneda p) where
  zeroP = proreturn zeroP
  ab >+< cd = proreturn (proextract ab >+< proextract cd)
instance Distributor p => Distributor (Coyoneda p) where
  optionalP = proreturn . optionalP . proextract
  manyP = proreturn . manyP . proextract

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
like `Alternative` but without requiring `Monoidal` structure,
and the `alternate` method, which is a lax monoidal structure morphism
on sums, with these laws relating them.

prop> left' = alternate . Left
prop> right' = alternate . Right
prop> zeroP = falseP
prop> x >+< y = alternate (Left x) >|< alternate (Right y)

For the case of `Functor`s, the analog of `alternate` can be defined
without any other constraint, but the case of `Profunctor`s turns
out to be slighly more complex, necessitating `CocartesianChoice`.

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

-- Alternator --

{- | The `Alternator` class co-extends `CocartesianChoice` and `Distributor`,
as well as `Alternative`, adding methods `someP` & `optionP`,
with these laws relating them.

prop> manyP p = optionP _Empty (someP p)
prop> optionalP p = optionP _Nothing (_Just >? p)
prop> someP p = p >:< manyP p

Its `Alternative` structure agrees with its `Alternator` structure,
`many` & `some` repeating an input for `manyP` & `someP`.

prop> empty = falseP
prop> (<|>) = (>|<)
prop> many = lmap repeat . manyP
prop> some = lmap repeat . someP

Not all `Distributor`s are `Alternator`s, in particular @(->)@ is
a `Distributor` but cannot be `Alternative`,
because there is no general polymorphic function @empty :: a -> b@,
so @(->)@ isn't an `Alternator`.

-}
class (Distributor p, CocartesianChoice p, forall x. Alternative (p x))
  => Alternator p where

    {- | One or more. -}
    someP :: p a b -> p [a] [b]
    someP x = x >:< manyP x

    {- | One or zero-with-default. -}
    optionP :: APrism a b () () {- ^ default -} -> p a b -> p a b
    optionP def p = p >|< pureP def

instance (Alternator p, Applicative f)
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
instance (Alternator p, Applicative f)
  => Alternator (WrappedPafb f p) where
    someP (WrapPafb x) = WrapPafb (rmap sequenceA (someP x))
    optionP def (WrapPafb x) = WrapPafb (optionP (prism pure pure . def) x)
instance Alternator p => CocartesianChoice (Coyoneda p) where
  alternate (Left p) = proreturn (alternate (Left (proextract p)))
  alternate (Right p) = proreturn (alternate (Right (proextract p)))
instance Alternator p => Alternator (Coyoneda p) where
  someP = proreturn . someP . proextract
  optionP def = proreturn . optionP def . proextract
instance Alternator p => CocartesianChoice (Yoneda p) where
  alternate (Left p) = proreturn (alternate (Left (proextract p)))
  alternate (Right p) = proreturn (alternate (Right (proextract p)))
instance Alternator p => Alternator (Yoneda p) where
  someP = proreturn . someP . proextract
  optionP def = proreturn . optionP def . proextract
instance Alternative f => CocartesianChoice (Joker f) where
  alternate (Left (Joker x)) = Joker (Left <$> x)
  alternate (Right (Joker y)) = Joker (Right <$> y)
instance Alternative f => Alternator (Joker f) where
  someP (Joker x) = Joker (some x)
  optionP def (Joker x) =
    Joker (x <|> withPrism def (\f _ -> pure (f ())))
