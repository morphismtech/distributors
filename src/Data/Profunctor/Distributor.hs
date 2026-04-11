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
  ( -- * Distributor
    Distributor (..)
  , dialt
    -- * Alternator
  , Alternator (..)
  , choice
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
import Data.Foldable hiding (toList)
import Data.Functor.Adjunction
import Data.Functor.Contravariant.Divisible
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
distributing an action over `[]` and `Maybe` datatypes,
which generalize to `Data.Traversable.Homogeneous.homogeneously`
distributing an action over homogeneous sum-of-products datatypes.

-}
class Monoidal p => Distributor p where

  {- | The zero structure morphism of a `Distributor`.

  `zeroP` has a default for `Alternator`s.

  prop> zeroP = empty
  -}
  zeroP :: p Void Void
  default zeroP :: Alternator p => p Void Void
  zeroP = empty

  {- | The sum structure morphism of a `Distributor`.

  `>+<` has a default for `Alternator`s.

  prop> x >+< y = alternate (Left x) <|> alternate (Right y)
  -}
  (>+<) :: p a b -> p c d -> p (Either a c) (Either b d)
  default (>+<)
    :: Alternator p
    => p a b -> p c d -> p (Either a c) (Either b d)
  x >+< y = alternate (Left x) <|> alternate (Right y)
  infixr 3 >+<

  {- | One or none. -}
  optionalP :: p a b -> p (Maybe a) (Maybe b)
  optionalP p = eotMaybe >~ p >+< oneP

  {- | Zero or more. -}
  manyP :: p a b -> p [a] [b]
  manyP p = eotList >~ p >*< manyP p >+< oneP

instance Distributor (->) where
  zeroP = id
  (>+<) = (+++)
instance Monoid s => Distributor (Forget s) where
  zeroP = Forget absurd
  Forget kL >+< Forget kR = Forget (either kL kR)
instance Decidable f => Distributor (Clown f) where
  zeroP = Clown lost
  Clown x >+< Clown y = Clown (chosen x y)
instance Alternative f => Distributor (Joker f) where
  zeroP = Joker empty
  Joker x >+< Joker y = Joker (Left <$> x <|> Right <$> y)
  optionalP (Joker x) = Joker (optional x)
  manyP (Joker x) = Joker (many x)
instance (Distributor p, Applicative f)
  => Distributor (WrappedPafb f p) where
    zeroP = WrapPafb (rmap pure zeroP)
    WrapPafb x >+< WrapPafb y = WrapPafb $
      dialt id (fmap Left) (fmap Right) x y
    manyP (WrapPafb x) = WrapPafb (rmap sequenceA (manyP x))
    optionalP (WrapPafb x) = WrapPafb (rmap sequenceA (optionalP x))
instance Applicative f => Distributor (Star f) where
  zeroP = Star absurd
  Star f >+< Star g =
    Star (either (fmap Left . f) (fmap Right . g))
  optionalP (Star f) = Star (traverse f)
  manyP (Star f) = Star (traverse f)
deriving via (Star m) instance Monad m => Distributor (Kleisli m)
instance Adjunction f u => Distributor (Costar f) where
  zeroP = Costar unabsurdL
  Costar f >+< Costar g = Costar (bimap f g . cozipL)
instance (Applicative f, Distributor p)
  => Distributor (Cayley f p) where
    zeroP = Cayley (pure zeroP)
    Cayley x >+< Cayley y = Cayley ((>+<) <$> x <*> y)
    optionalP (Cayley x) = Cayley (optionalP <$> x)
    manyP (Cayley x) = Cayley (manyP <$> x)
instance (ArrowZero p, ArrowChoice p)
  => Distributor (Pro.WrappedArrow p) where
    zeroP = zeroArrow
    (>+<) = (+++)
deriving via (Pro.WrappedArrow p)
  instance (ArrowZero p, ArrowChoice p)
    => Distributor (Ap.WrappedArrow p)
instance (Distributor p, Distributor q)
  => Distributor (Procompose p q) where
    zeroP = Procompose zeroP zeroP
    Procompose xL yL >+< Procompose xR yR =
      Procompose (xL >+< xR) (yL >+< yR)
    optionalP (Procompose f g) =
      Procompose (optionalP f) (optionalP g)
    manyP (Procompose f g) =
      Procompose (manyP f) (manyP g)
instance (Distributor p, Distributor q)
  => Distributor (Product p q) where
    zeroP = Pair zeroP zeroP
    Pair x0 y0 >+< Pair x1 y1 = Pair (x0 >+< x1) (y0 >+< y1)
    optionalP (Pair f g) =
      Pair (optionalP f) (optionalP g)
    manyP (Pair f g) =
      Pair (manyP f) (manyP g)
instance Distributor p => Distributor (Yoneda p) where
  zeroP = proreturn zeroP
  ab >+< cd = proreturn (proextract ab >+< proextract cd)
  optionalP = proreturn . optionalP . proextract
  manyP = proreturn . manyP . proextract
instance Distributor p => Distributor (Coyoneda p) where
  zeroP = proreturn zeroP
  ab >+< cd = proreturn (proextract ab >+< proextract cd)
  optionalP = proreturn . optionalP . proextract
  manyP = proreturn . manyP . proextract

{- | `dialt` is a functionalized form of `>+<`. -}
dialt
  :: Distributor p
  => (s -> Either a c)
  -> (b -> t)
  -> (d -> t)
  -> p a b -> p c d -> p s t
dialt f g h p q = dimap f (either g h) (p >+< q)

-- Alternator --

{- | The `Alternator` class co-extends `Choice` and `Distributor`,
as well as `Alternative`, adding the `alternate` method,
which is a lax monoidal structure morphism on sums,
and methods `someP` & `optionP`,
with these these laws relating them.

prop> left' = alternate . Left
prop> right' = alternate . Right
prop> zeroP = empty
prop> x >+< y = alternate (Left x) <|> alternate (Right y)
prop> manyP p = optionP _Empty (someP p)
prop> optionalP p = optionP _Nothing (_Just >? p)
prop> someP p = p >:< manyP p

For the case of `Functor`s, the analog of `alternate` can be defined
without any other constraint, but the case of `Profunctor`s turns
out to be slighly more complex, necessitating `Alternator`.

>>> :{
alternateF :: Functor f => Either (f a) (f b) -> f (Either a b)
alternateF = either (fmap Left) (fmap Right)
:}

Not all `Distributor`s are `Alternator`s, in particular @(->)@ is
a `Distributor` but cannot be `Alternative`,
because there is no `empty` function for any @a -> b@,
so @(->)@ isn't an `Alternator`.

-}
class (Choice p, Distributor p, forall x. Alternative (p x))
  => Alternator p where

    {- | The structure morphism for an `Alternator`,
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

    {- | One or more. -}
    someP :: p a b -> p [a] [b]
    someP x = x >:< manyP x

    {- | One or zero-with-default. -}
    optionP :: APrism a b () () {- ^ default -} -> p a b -> p a b
    optionP def p = p <|> pureP def

-- | Combines all `Alternative` choices in the specified list.
choice :: (Foldable f, Alternative p) => f (p a) -> p a
choice = foldl' (<|>) empty

instance (Alternator p, Applicative f)
  => Alternator (WrappedPafb f p) where
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

    someP (WrapPafb x) = WrapPafb (rmap sequenceA (someP x))
instance Alternator p => Alternator (Coyoneda p) where
  alternate (Left p) = proreturn (alternate (Left (proextract p)))
  alternate (Right p) = proreturn (alternate (Right (proextract p)))
  someP = proreturn . someP . proextract
instance Alternator p => Alternator (Yoneda p) where
  alternate (Left p) = proreturn (alternate (Left (proextract p)))
  alternate (Right p) = proreturn (alternate (Right (proextract p)))
  someP = proreturn . someP . proextract
