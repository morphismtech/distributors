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
  , replicateP, (>:<), asEmpty
  , meander, eotFunList
  ) where

import Control.Applicative hiding (WrappedArrow)
import Control.Applicative qualified as Ap (WrappedArrow)
import Control.Arrow
import Control.Lens hiding (chosen)
import Control.Lens.Internal.Context
import Control.Lens.Internal.Prism
import Control.Lens.Internal.Profunctor
import Control.Lens.PartialIso
import Data.Bifunctor.Clown
import Data.Bifunctor.Joker
import Data.Bifunctor.Product
import Data.Distributive
import Data.Functor.Compose
import Data.Functor.Contravariant.Divisible
import Data.Profunctor hiding (WrappedArrow)
import Data.Profunctor qualified as Pro (WrappedArrow)
import Data.Profunctor.Cayley
import Data.Profunctor.Composition
import Data.Profunctor.Monad
import Data.Profunctor.Yoneda

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
  => (s -> a)
  -> (s -> c)
  -> (b -> d -> t)
  -> p a b -> p c d -> p s t
dimap2 f g h p q = liftA2 h (lmap f p) (lmap g q)

{- | `foreverP` repeats an action indefinitely;
analagous to `Control.Monad.forever`, extending it to `Monoidal`. -}
foreverP :: Monoidal p => p () c -> p a b
foreverP a = let a' = a >* a' in a'

{- | A `Monoidal` & `Choice` nil operator. -}
asEmpty :: (AsEmpty s, Monoidal p, Choice p) => p s s
asEmpty = _Empty >? oneP

{- | A `Monoidal` & `Choice` cons operator. -}
(>:<) :: (Cons s t a b, Monoidal p, Choice p) => p a b -> p s t -> p s t
x >:< xs = _Cons >? x >*< xs
infixr 5 >:<

{- | Thanks to Fy on Monoidal Café Discord.

A `Traversable` & `Data.Distributive.Distributive` type
is a homogeneous countable product.
That means it is a static length container, so unlike `replicateP`,
`ditraverse` does not need an `Int` argument.
-}
ditraverse
  :: (Traversable t, Distributive t, Monoidal p)
  => p a b -> p (t a) (t b)
ditraverse p = traverse (\f -> lmap f p) (distribute id)

{- | `replicateP` is analagous to `Control.Monad.replicateM`,
for `Monoidal` & `Choice` `Profunctor`s. When the number
of repetitions is less than or equal to 0, it returns `asEmpty`.
-}
replicateP
  :: (Monoidal p, Choice p, AsEmpty s, Cons s s a a)
  => Int {- ^ number of repetitions -} -> p a a -> p s s
replicateP n _ | n <= 0 = asEmpty
replicateP n a = a >:< replicateP (n-1) a

{- | For any `Monoidal`, `Choice` & `Strong` `Profunctor`,
`meander` is invertible and gives a default implementation for the
`Data.Profunctor.Traversing.wander`
method of `Data.Profunctor.Traversing.Traversing`,
though `Strong` is not needed for its definition.

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
  MoreFun a f -> ($) <$> f <*> sell a
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

-- Orphanage --

instance Monoid r => Applicative (Forget r a) where
  pure _ = Forget mempty
  Forget f <*> Forget g = Forget (f <> g)
instance Decidable f => Applicative (Clown f a) where
  pure _ = Clown conquer
  Clown x <*> Clown y = Clown (divide (id &&& id) x y)
deriving newtype instance Applicative f => Applicative (Joker f a)
deriving via Compose (p a) f instance
  (Profunctor p, Applicative (p a), Applicative f)
    => Applicative (WrappedPafb f p a)
deriving via Compose (p a) f instance
  (Profunctor p, Alternative (p a), Applicative f)
    => Alternative (WrappedPafb f p a)
instance (Closed p, Distributive f)
  => Closed (WrappedPafb f p) where
    closed (WrapPafb p) = WrapPafb (rmap distribute (closed p))
deriving via (Ap.WrappedArrow p a) instance Arrow p
  => Functor (Pro.WrappedArrow p a)
deriving via (Ap.WrappedArrow p a) instance Arrow p
  => Applicative (Pro.WrappedArrow p a)
deriving via (Pro.WrappedArrow p) instance Arrow p
  => Profunctor (Ap.WrappedArrow p)
instance (Monoidal p, Applicative (q a))
  => Applicative (Procompose p q a) where
    pure b = Procompose (pure b) (pure b)
    Procompose wb aw <*> Procompose vb av = Procompose
      (dimap2 fst snd ($) wb vb)
      (liftA2 (,) aw av)
instance (Monoidal p, Monoidal q)
  => Applicative (Product p q a) where
    pure b = Pair (pure b) (pure b)
    Pair x0 y0 <*> Pair x1 y1 = Pair (x0 <*> x1) (y0 <*> y1)
instance (Functor f, Functor (p a)) => Functor (Cayley f p a) where
  fmap f (Cayley x) = Cayley (fmap (fmap f) x)
instance (Applicative f, Applicative (p a)) => Applicative (Cayley f p a) where
  pure b = Cayley (pure (pure b))
  Cayley x <*> Cayley y = Cayley ((<*>) <$> x <*> y)
instance (Profunctor p, Applicative (p a))
  => Applicative (Yoneda p a) where
    pure = proreturn . pure
    ab <*> cd = proreturn (proextract ab <*> proextract cd)
instance (Profunctor p, Applicative (p a))
  => Applicative (Coyoneda p a) where
    pure = proreturn . pure
    ab <*> cd = proreturn (proextract ab <*> proextract cd)
instance (Profunctor p, Alternative (p a))
  => Alternative (Yoneda p a) where
    empty = proreturn empty
    ab <|> cd = proreturn (proextract ab <|> proextract cd)
    many = proreturn . many . proextract
instance (Profunctor p, Alternative (p a))
  => Alternative (Coyoneda p a) where
    empty = proreturn empty
    ab <|> cd = proreturn (proextract ab <|> proextract cd)
    many = proreturn . many . proextract
instance Applicative (Market a b s) where
  pure t = Market (pure t) (pure (Left t))
  Market f0 g0 <*> Market f1 g1 = Market
    (\b -> f0 b (f1 b))
    (\s ->
      case g0 s of
        Left bt -> case g1 s of
          Left b -> Left (bt b)
          Right a -> Right a
        Right a -> Right a
    )
