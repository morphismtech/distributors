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
  , skipManyP
  , skipOptionalP
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
import Data.Maybe (isJust)

-- $setup
-- >>> import Data.Bifunctor.Joker (Joker (..))
-- >>> import Data.Profunctor.Monoidal ((*<))
-- >>> import Text.ParserCombinators.ReadP (char, readP_to_S)

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
  optionalP p = eotMaybe . swapped >~ p >+< oneP

  {- | Zero or more. -}
  manyP :: p a b -> p [a] [b]
  manyP p = let ps = eotList . swapped >~ p >*< ps >+< oneP in ps

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

{- | Zero or more, skipped: sequencing any number of actions forwards,
& none backwards, like whitespace that a parser accepts
& a printer omits.

> prop> skipManyP p = dimap (const []) (const ()) (manyP p)

>>> [r | (r, "") <- readP_to_S (runJoker (skipManyP (Joker (char ' ')) *< Joker (char 'x'))) "   x"]
[()]
-}
skipManyP :: Distributor p => p a b -> p () ()
skipManyP p = dimap (const []) (const ()) (manyP p)

{- | Zero or one, skipped: sequencing one action or none forwards,
& none backwards, like a trailing separator that a parser accepts
& a printer omits.

>>> [r | (r, "") <- readP_to_S (runJoker (Joker (char 'x') *< skipOptionalP (Joker (char ',')))) "x,"]
"x"
-}
skipOptionalP :: Distributor p => p a b -> p () ()
skipOptionalP p = dimap (const Nothing) (const ()) (optionalP p)

-- Alternator --

{- | The `Alternator` class co-extends `CocartesianChoice` and `Distributor`,
as well as `Alternative`, adding methods `someP` & `optionP`,
with these laws relating them.

> prop> manyP p = optionP _Empty (someP p)
> prop> optionalP p = optionP _Nothing (_Just >? p)
> prop> someP p = p >:< manyP p

These mirror the laws of a `KleeneStarAlgebra`, @starK x = optK (plusK x)@
& @plusK x = x <> starK x@, unfolding `someP` on the left.
Its unfolding on the right, @someP p = snocP (manyP p) p@,
mirroring @plusK x = starK x <> x@, isn't a law though,
since a greedy or predictive parser's `manyP` consumes every @p@,
leaving none for the last; only a backtracking one finds it.

Its `Alternative` structure agrees with its `Alternator` structure,
`many` & `some` repeating an input for `manyP` & `someP`.

> prop> empty = falseP
> prop> (<|>) = (>|<)
> prop> many = lmap repeat . manyP
> prop> some = lmap repeat . someP

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

    {- | Zero or more, then the rest, @p* q@, trying the rest first,
    like @manyTill@ of [parsec](https://hackage.haskell.org/package/parsec),
    the least solution of its unfolding.

    > prop> manyTillP p q = q >|< p >:< manyTillP p q
    > prop> manyTillP falseP q = q

    It mirrors a `KleeneStarAlgebra`'s @starK x <> y@, so that
    a static `Alternator`, which sequences no input, may define it
    without recursing, as an input-consuming one, like a parser
    or printer, can't, since only consuming finds where @q@ begins.
    It recognizes what @manyP p@ does with @q = `asEmpty`@,
    but trying fewer @p@s first, rather than more.
    -}
    manyTillP :: p a b -> p [a] [b] -> p [a] [b]
    manyTillP p q = let r = q >|< p >:< r in r

    {- | Between some numbers of times, inclusive, at least a lower bound,
    & at most an upper bound, if there's one, like a regular expression's
    @{lo,hi}@, or @{lo,}@. It takes the mandatory times first, then,
    unbounded, `someP` or `manyP`, or, bounded, the optional times,
    trying more first. It never matches where @lo > hi@,
    nor where @hi@ is negative, its counts being those @n >= 0@ within
    its bounds.

    It mirrors a `KleeneStarAlgebra`'s `timesK`, so that a static
    `Alternator` may keep its counts, rather than unfolding them.

    > prop> timesP 0 Nothing = manyP
    > prop> timesP 1 Nothing = someP
    > prop> timesP n (Just n) = replicateP n, for @n >= 0@
    -}
    timesP :: Int -> Maybe Int -> p a b -> p [a] [b]
    timesP lo hi p
      | lo < 0 = timesP 0 hi p
      | maybe False (lo >) hi = empty
      | lo > 1 || (lo == 1 && isJust hi) =
          p >:< timesP (lo - 1) (subtract 1 <$> hi) p
      | lo == 1 = someP p
      | otherwise = case hi of
          Nothing -> manyP p
          Just m
            | m <= 0 -> eotList . swapped >~ empty >+< oneP
            | otherwise ->
                eotList . swapped >~ p >*< timesP 0 (Just (m - 1)) p >+< oneP

instance (Alternator p, Applicative f)
  => Alternator (WrappedPafb f p) where
    someP (WrapPafb x) = WrapPafb (rmap sequenceA (someP x))
    optionP def (WrapPafb x) = WrapPafb (optionP (prism pure pure . def) x)
    timesP lo hi (WrapPafb x) = WrapPafb (rmap sequenceA (timesP lo hi x))
instance Alternator p => Alternator (Coyoneda p) where
  someP = proreturn . someP . proextract
  optionP def = proreturn . optionP def . proextract
  manyTillP p q = proreturn (manyTillP (proextract p) (proextract q))
  timesP lo hi = proreturn . timesP lo hi . proextract
instance Alternator p => Alternator (Yoneda p) where
  someP = proreturn . someP . proextract
  optionP def = proreturn . optionP def . proextract
  manyTillP p q = proreturn (manyTillP (proextract p) (proextract q))
  timesP lo hi = proreturn . timesP lo hi . proextract
instance Alternative f => Alternator (Joker f) where
  someP (Joker x) = Joker (some x)
  optionP def (Joker x) =
    Joker (x <|> withPrism def (\f _ -> pure (f ())))
