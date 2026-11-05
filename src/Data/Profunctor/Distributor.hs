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
import Data.Profunctor.Monoidal.Cocartesian

-- Distributor --

{- | A `Distributor`, or lax distributive profunctor,
respects [distributive category]
(https://ncatlab.org/nlab/show/distributive+category)
structure, that is nilary and binary products and coproducts,
@()@, @(,)@, `Data.Void.Void` and `Either`, being both
`Monoidal` and `CocartesianMonoidal`.

`Distributor` additionally has methods `manyP` & `optionalP`,
distributing an action over @[]@ and `Maybe` datatypes,
which generalize to `Data.Traversable.Homogeneous.homogeneously`
distributing an action over
`Data.Traversable.Homogeneous.Homogeneous`
sum-of-products datatypes.
-}
class (Monoidal p, CocartesianMonoidal p) => Distributor p where

  {- | One or none. -}
  optionalP :: p a b -> p (Maybe a) (Maybe b)
  optionalP p = eotMaybe >~ p >+< oneP

  {- | Zero or more. -}
  manyP :: p a b -> p [a] [b]
  manyP p = eotList >~ p >*< manyP p >+< oneP

instance Distributor (->)
instance Monoid s => Distributor (Forget s)
instance Decidable f => Distributor (Clown f)
instance Alternative f => Distributor (Joker f) where
  optionalP (Joker x) = Joker (optional x)
  manyP (Joker x) = Joker (many x)
instance (Distributor p, Applicative f)
  => Distributor (WrappedPafb f p) where
    manyP (WrapPafb x) = WrapPafb (rmap sequenceA (manyP x))
    optionalP (WrapPafb x) = WrapPafb (rmap sequenceA (optionalP x))
instance Applicative f => Distributor (Star f) where
  optionalP (Star f) = Star (traverse f)
  manyP (Star f) = Star (traverse f)
deriving via (Star m) instance Monad m => Distributor (Kleisli m)
instance Adjunction f u => Distributor (Costar f)
instance (Applicative f, Distributor p)
  => Distributor (Cayley f p) where
    optionalP (Cayley x) = Cayley (optionalP <$> x)
    manyP (Cayley x) = Cayley (manyP <$> x)
instance (ArrowZero p, ArrowChoice p)
  => Distributor (Pro.WrappedArrow p)
deriving via (Pro.WrappedArrow p)
  instance (ArrowZero p, ArrowChoice p)
    => Distributor (Ap.WrappedArrow p)
instance (Distributor p, Distributor q)
  => Distributor (Procompose p q) where
    optionalP (Procompose f g) =
      Procompose (optionalP f) (optionalP g)
    manyP (Procompose f g) =
      Procompose (manyP f) (manyP g)
instance (Distributor p, Distributor q)
  => Distributor (Product p q) where
    optionalP (Pair f g) =
      Pair (optionalP f) (optionalP g)
    manyP (Pair f g) =
      Pair (manyP f) (manyP g)
instance Distributor p => Distributor (Yoneda p) where
  optionalP = proreturn . optionalP . proextract
  manyP = proreturn . manyP . proextract
instance Distributor p => Distributor (Coyoneda p) where
  optionalP = proreturn . optionalP . proextract
  manyP = proreturn . manyP . proextract

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
  => Alternator (WrappedPafb f p) where
    someP (WrapPafb x) = WrapPafb (rmap sequenceA (someP x))
    optionP def (WrapPafb x) = WrapPafb (optionP (prism pure pure . def) x)
instance Alternator p => Alternator (Coyoneda p) where
  someP = proreturn . someP . proextract
  optionP def = proreturn . optionP def . proextract
instance Alternator p => Alternator (Yoneda p) where
  someP = proreturn . someP . proextract
  optionP def = proreturn . optionP def . proextract
instance Alternative f => Alternator (Joker f) where
  someP (Joker x) = Joker (some x)
  optionP def (Joker x) =
    Joker (x <|> withPrism def (\f _ -> pure (f ())))
