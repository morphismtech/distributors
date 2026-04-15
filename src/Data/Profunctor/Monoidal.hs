{-# OPTIONS_GHC -Wno-orphans #-}

{-|
Module      : Data.Profunctor.Monoidal
Description : monoidal profunctors
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Data.Profunctor.Monoidal
  ( -- * Monoidal
    Monoidal
  , oneP, (>*<), (>*), (*<)
  , dimap2, foreverP, ditraverse
    -- * Monoidal & Choice
  , pureP, asEmpty, (>:<), replicateP, onlyOne
  , meander, eotFunList
  ) where

import Control.Lens
import Control.Lens.Internal.Context
import Control.Lens.PartialIso
import Data.Distributive
import GHC.IsList

-- Monoidal --

{- | A lax `Monoidal` product `Profunctor` has unit `oneP`
and product `>*<` lax monoidal structure morphisms.
This is equivalent to the `Profunctor` also being `Applicative`.

Laws:

>>> let lunit = dimap (\((),a) -> a) (\a -> ((),a))
>>> let runit = dimap (\(a,()) -> a) (\a -> (a,()))
>>> let assoc = dimap (\(a,(b,c)) -> ((a,b),c)) (\((a,b),c) -> (a,(b,c)))

prop> oneP >*< p = lunit p
prop> p >*< oneP = runit p
prop> p >*< q >*< r = assoc ((p >*< q) >*< r)
prop> dimap (f >*< g) (h >*< i) (p >*< q) = dimap f h p >*< dimap g i q

-}
type Monoidal p = (Profunctor p, forall x. Applicative (p x))

{- | `oneP` is the unit of a `Monoidal` `Profunctor`. -}
oneP :: Monoidal p => p () ()
oneP = pure ()

{- | `>*<` is the product of a `Monoidal` `Profunctor`. -}
(>*<) :: Monoidal p => p a b -> p c d -> p (a,c) (b,d)
(>*<) = dimap2 fst snd (,)
infixr 5 >*<

{- | `>*` sequences actions, discarding the value of the first argument;
analagous to `*>`, extending it to `Monoidal`.

prop> oneP >* p = p

-}
(>*) :: Monoidal p => p () c -> p a b -> p a b
x >* y = lmap (const ()) x *> y
infixl 6 >*

{- | `*<` sequences actions, discarding the value of the second argument;
analagous to `<*`, extending it to `Monoidal`.

prop> p *< oneP = p

-}
(*<) :: Monoidal p => p a b -> p () c -> p a b
x *< y = x <* lmap (const ()) y
infixl 6 *<

{- | `dimap2` is a curried, functionalized form of `>*<`,
analagous to `liftA2`. -}
dimap2
  :: Monoidal p
  => (s -> a) -- ^ first projection, e.g. `fst`
  -> (s -> c) -- ^ second projection, e.g. `snd`
  -> (b -> d -> t) -- ^ pairing function, e.g. @(,)@
  -> p a b -> p c d -> p s t
dimap2 f g h p q = liftA2 h (lmap f p) (lmap g q)

{- | `foreverP` repeats an action a countable infinity of times;
analagous to `Control.Monad.forever`, extending it to `Monoidal`. -}
foreverP :: Monoidal p => p () c -> p a b
foreverP a = let a' = a >* a' in a'

{- | Thanks to Fy on Monoidal Café Discord.

A `Traversable` & `Data.Distributive.Distributive` type
is a homogeneous countable product.
That means it is a static countable-length container,
so unlike `replicateP`, `ditraverse` doesn't need
an additional argument for number of repetitions.
-}
ditraverse
  :: (Traversable t, Distributive t, Monoidal p)
  => p a b -> p (t a) (t b)
ditraverse p = traverse (\f -> lmap f p) (distribute id)

{- | Lift a single bidirectional element
into a `Monoidal` & `Choice` structure.
Bidirectionality is encoded by `APrism`.
Singularity is encoded by the unit type @()@.
Bidirectional elements can be generated from
nilary constructors of algebraic datatypes using `makeNestedPrisms`,
from terms of a type with an `Eq` instance using `only`,
from nil elements using `_Empty`,
or from any `.`-composition of `Control.Lens.Prism.Prism`s
terminating with a bidirectional element.
-}
pureP
  :: (Monoidal p, Choice p)
  => APrism a b () () -- ^ bidirectional element
  -> p a b
pureP pattern = pattern >? oneP

{- | A `Monoidal` & `Choice` nil combinator. -}
asEmpty :: (AsEmpty s, Monoidal p, Choice p) => p s s
asEmpty = pureP _Empty

{- | A `Monoidal` & `Choice` cons combinator. -}
(>:<) :: (Cons s t a b, Monoidal p, Choice p) => p a b -> p s t -> p s t
x >:< xs = _Cons >? x >*< xs
infixr 5 >:<

{- | Use when `IsList` with `onlyOne` `Item`. -}
onlyOne
  :: (Monoidal p, Choice p, IsList s)
  => p (Item s) (Item s) -> p s s
onlyOne p = iso toList (fromListN 1) >? p >:< asEmpty

{- | `replicateP` is analagous to `Control.Monad.replicateM`,
for `Monoidal` & `Choice` `Profunctor`s. When the number
of repetitions is less than or equal to 0, it returns `asEmpty`.
-}
replicateP
  :: (Monoidal p, Choice p, AsEmpty s, Cons s s a a)
  => Int {- ^ number of repetitions -} -> p a a -> p s s
replicateP n _ | n <= 0 = asEmpty
replicateP n a = a >:< replicateP (n-1) a

{- | For any `Monoidal`, `Choice` & `Data.Profunctor.Strong` `Profunctor`,
`meander` is invertible and gives a default implementation for the
`Data.Profunctor.Traversing.wander`
method of `Data.Profunctor.Traversing.Traversing`,
though `Data.Profunctor.Strong` is not needed for its definition.

See Pickering, Gibbons & Wu,
[Profunctor Optics - Modular Data Accessors](https://arxiv.org/abs/1703.10857)
-}
meander
  :: (Monoidal p, Choice p)
  => ATraversal s t a b -> p a b -> p s t
meander f = dimap (f sell) iextract . meandering
  where
    meandering
      :: (Monoidal q, Choice q)
      => q u v -> q (Bazaar (->) u w x) (Bazaar (->) v w x)
    meandering q = eotFunList >~ right' (q >*< meandering q)

{- |
`eotFunList` is used to define `meander`.
See van Laarhoven, [A non-regular data type challenge]
(https://twanvl.nl/blog/haskell/non-regular1),
both post and comments, for details.
-}
eotFunList :: Iso
  (Bazaar (->) a1 b1 t1) (Bazaar (->) a2 b2 t2)
  (Either t1 (a1, Bazaar (->) a1 b1 (b1 -> t1)))
  (Either t2 (a2, Bazaar (->) a2 b2 (b2 -> t2)))
eotFunList = iso (f . toFun) (fromFun . g) where
  f = \case
    DoneFun t -> Left t
    MoreFun a baz -> Right (a, baz)
  g = \case
    Left t -> DoneFun t
    Right (a, baz) -> MoreFun a baz
data FunList a b t
  = DoneFun t
  | MoreFun a (Bazaar (->) a b (b -> t))
toFun :: Bazaar (->) a b t -> FunList a b t
toFun (Bazaar f) = f sell
fromFun :: FunList a b t -> Bazaar (->) a b t
fromFun = \case
  DoneFun t -> pure t
  MoreFun a f -> flip ($) <$> sell a <*> f
instance Functor (FunList a b) where
  fmap f = \case
    DoneFun t -> DoneFun (f t)
    MoreFun a h -> MoreFun a (fmap (f .) h)
instance Applicative (FunList a b) where
  pure = DoneFun
  (<*>) = \case
    DoneFun t -> fmap t
    MoreFun a h -> \l ->
      MoreFun a (flip <$> h <*> fromFun l)
instance Sellable (->) FunList where sell b = MoreFun b (pure id)
