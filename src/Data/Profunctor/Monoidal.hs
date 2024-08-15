{-|
Module      : Data.Profunctor.Monoidal
Description : lax monoidal profunctors
Copyright   : (c) Eitan Chatav, 2023
License     : LICENSE
Maintainer  : eitan.chatav@gmail.com
Stability   : experimental


This module defines types and terms for lax monoidal
profunctors, which are analogous to `Applicative` `Functor`s.
It also provides functions which define
`Control.Lens.Traversal.Traversal` optics
in a profunctor representation using `Strong` and `Choice`,
`Monoidal` `Profunctor`s.
-}
module Data.Profunctor.Monoidal
  ( -- * Lax Monoidal Profunctors
    Monoidal (..)
  , dimap2
  , (>*)
  , (*<)
  , (>:<)
  , pureP
  , apP
  , liftA2P
  , replicateP
  , replicateP'
  , replicateP_
  , foreverP
    -- * Free Monoidal Profunctors
  , Mon (..)
  , liftMon
  , hoistMon
  , foldMon
  , ChooseMon (..)
  , liftChooseMon
  , hoistChooseMon
  , foldChooseMon
  , ChooseMonF (..)
    -- * Monoidal types
  , WrappedMonoidal (..)
  , Shop (..)
  , runShop
  , FunList (..)
  , funListBazaar
  , Purchase (..)
  , buy
  ) where

import Control.Arrow
import Control.Comonad
import Control.Lens hiding (chosen, Traversing)
import Control.Lens.Internal.Bazaar
import Control.Lens.Internal.Context
import Control.Lens.PartialIso
import Control.Lens.Stream
import Control.Monad
import Data.Bifunctor.Biff
import Data.Bifunctor.Clown
import Data.Bifunctor.Joker
import Data.Bifunctor.Product
import Data.Bifunctor.Tannen
import Data.Functor.Contravariant.Divisible hiding (chosen)
import Data.Profunctor hiding (WrappedArrow(..))
import qualified Data.Profunctor as Pro (WrappedArrow(..))
import Data.Profunctor.Cayley
import Data.Profunctor.Composition
import Data.Profunctor.Monad
import Data.Profunctor.Traversing
import Data.Profunctor.Yoneda
import Witherable

{- | A lax monoidal profunctor with respect to product
or simply a product profunctor
respects the monoidal structure given by
the nilary and binary products,
@()@ and @(,)@.

Laws:

>>> let (f >< g) (a,c) = (f a, g c)
>>> let lunit = dimap (\((),a) -> a) (\a -> ((),a))
>>> let runit = dimap (\(a,()) -> a) (\a -> (a,()))
>>> let assoc = dimap (\(a,(b,c)) -> ((a,b),c)) (\((a,b),c) -> (a,(b,c)))
prop> dimap (f >< g) (h >< i) (p >*< q) = dimap f h p >*< dimap g i q
prop> oneP >*< p = lunit p
prop> p >*< oneP = runit p
prop> p >*< q >*< r = assoc ((p >*< q) >*< r)

The defining methods for the `Monoidal` class are inspired by
section 7 of the functional pearl
[Applicative Programming with Effects]
(https://www.staff.city.ac.uk/~ross/papers/Applicative.pdf).

`Monoidal` has a default implementation when
the `Profunctor` is also `Applicative`. Indeed,
`Monoidal` is equivalent to an `Applicative` `Profunctor` with

prop> pure = pureP
prop> (<*>) = apP
-}
class Profunctor p => Monoidal p where

  {- |
  `oneP` is a symmetric analog of `pureP`.

  prop> oneP = pure ()
  -}
  oneP :: p () ()
  default oneP :: (forall x. Applicative (p x)) => p () ()
  oneP = pure ()

  {- |
  `>*<` is a symmetrical analog of `dimap2`.

  prop> x >*< y = (,) <$> lmap fst x <*> lmap snd y
  -}
  (>*<) :: p a b -> p c d -> p (a,c) (b,d)
  infixr 4 >*<
  default (>*<)
    :: (forall x. Applicative (p x))
    => p a b -> p c d -> p (a,c) (b,d)
  x >*< y = (,) <$> lmap fst x <*> lmap snd y

instance Monoidal (->) where
  oneP = id
  (>*<) = (***)
instance Monoid s => Monoidal (Forget s) where
  oneP = Forget mempty
  Forget f >*< Forget g = Forget (\(a,c) -> f a <> g c)
instance Divisible f => Monoidal (Clown f) where
  oneP = Clown conquer
  Clown x >*< Clown y = Clown (divided x y)
instance Applicative f => Monoidal (Joker f) where
  oneP = Joker (pure ())
  Joker x >*< Joker y = Joker ((,) <$> x <*> y)
instance Arrow p => Monoidal (Pro.WrappedArrow p) where
  oneP = Pro.WrapArrow returnA
  Pro.WrapArrow p >*< Pro.WrapArrow q = Pro.WrapArrow (p *** q)
instance (Monoidal p, Monoidal q)
  => Monoidal (Procompose p q) where
    oneP = Procompose oneP oneP
    Procompose wb aw >*< Procompose vb av =
      Procompose (wb >*< vb) (aw >*< av)
instance (Monoidal p, Monoidal q)
  => Monoidal (Product p q) where
    oneP = Pair oneP oneP
    Pair x0 y0 >*< Pair x1 y1 = Pair (x0 >*< x1) (y0 >*< y1)
instance Functor f => Monoidal (Costar f) where
  oneP = Costar (const ())
  Costar f >*< Costar g =
    Costar (\ac -> (f (fst <$> ac), g (snd <$> ac)))
instance Applicative f => Monoidal (Star f) where
  oneP = Star (const (pure ()))
  Star f >*< Star g =
    Star (\(a,c) -> (,) <$> f a <*> g c)
deriving via (Star m) instance Monad m => Monoidal (Kleisli m)
instance (Applicative f, Monoidal p) => Monoidal (Tannen f p) where
  oneP = Tannen (pure oneP)
  Tannen x >*< Tannen y = Tannen ((>*<) <$> x <*> y)
instance (Applicative f, Monoidal p) => Monoidal (Cayley f p) where
  oneP = Cayley (pure oneP)
  Cayley x >*< Cayley y = Cayley ((>*<) <$> x <*> y)
instance (Functor f, Applicative g, Monoidal p)
  => Monoidal (Biff p f g) where
    oneP = Biff (dimap (const ()) pure oneP)
    Biff x >*< Biff y = Biff $ dimap
      ((fst <$>) &&& (snd <$>))
      (uncurry (liftA2 (,)))
      (x >*< y)
instance Monoid s => Monoidal (PartialExchange s t)
instance Monoidal p => Monoidal (Yoneda p) where
  oneP = proreturn oneP
  ab >*< cd = proreturn (proextract ab >*< proextract cd)
instance Monoidal p => Monoidal (Coyoneda p) where
  oneP = proreturn oneP
  ab >*< cd = proreturn (proextract ab >*< proextract cd)

{- | Like `pure` but with a `Monoidal` constraint,
`pureP` is a functionalization of `oneP`.

prop> pure = pureP
-}
pureP :: Monoidal p => b -> p a b
pureP b = dimap (const ()) (const b) oneP

{- | `dimap2` is a fully curried functionalization of `>*<`. -}
dimap2
  :: Monoidal p
  => (s -> a)
  -> (s -> c)
  -> (b -> d -> t)
  -> p a b -> p c d -> p s t
dimap2 f g h p q = dimap (f &&& g) (uncurry h) (p >*< q)

{- | Like `liftA2` but with a `Monoidal` constraint.

prop> liftA2 = liftA2P
-}
liftA2P :: Monoidal p => (b -> c -> d) -> p a b -> p a c -> p a d
liftA2P = dimap2 id id

{- | Like `<*>` but with a `Monoidal` constraint.

prop> (<*>) = apP
-}
apP :: Monoidal p => p a (b -> d) -> p a b -> p a d
apP = liftA2P ($)

{- | Analogous to `*>` but with a `Monoidal` constraint.

prop> (*>) = (>*)
-}
(>*) :: Monoidal p => p () c -> p a b -> p a b
x >* y = dimap ((),) snd (x >*< y)
infixr 5 >*

{- | Analogous to `<*` but with a `Monoidal` constraint.

prop> (<*) = (*<)
-}
(*<) :: Monoidal p => p a b -> p () c -> p a b
x *< y = dimap (,()) fst (x >*< y)
infixr 5 *<

{- | Bidirectional consing. -}
(>:<) :: (Cons s t a b, Monoidal p, Choice p) => p a b -> p s t -> p s t
ab >:< st = _Cons >? ab >*< st
infixr 6 >:<

{- | `replicateP` is analogous to `replicateM`. -}
replicateP
  :: (Monoidal p, Choice p, Cochoice p, Stream s t a b)
  => Int -> p a b -> p s t
replicateP n _ | n <= 0 = _Null >?< oneP
replicateP n p = p >:< replicateP (n-1) p

{- | `replicateP'` is a simple analog to `replicateM`. -}
replicateP'
  :: (Monoidal p, Choice p, SimpleStream s a)
  => Int -> p a a -> p s s
replicateP' n _ | n <= 0 = _Nil >? oneP
replicateP' n p = p >:< replicateP' (n-1) p

{- | `replicateP_` is like `replicateM_`. -}
replicateP_ :: Monoidal p => Int -> p () c -> p a ()
replicateP_ n _ | n <= 0 = pureP ()
replicateP_ n p = p >* replicateP_ (n-1) p

{- | `foreverP` is like `forever`. -}
foreverP :: Monoidal p => p () c -> p a b
foreverP p = let p' = p >* p' in p'

{- | A free `Monoidal` `Profunctor` type. -}
data Mon p a b where
  MonPure :: b -> Mon p a b
  MonAp
    :: (s -> a)
    -> Mon p s (b -> t)
    -> p a b
    -> Mon p s t

{- | Lifts base terms to `Mon`. -}
liftMon :: p a b -> Mon p a b
liftMon p = MonAp id (MonPure id) p

{- | Hoists base functions to `Mon`. -}
hoistMon
  :: (forall x y. p x y -> q x y)
  -> Mon p a b -> Mon q a b
hoistMon h = \case
  MonPure b -> MonPure b
  MonAp f g x -> MonAp f (hoistMon h g) (h x)

{- | Folds functions to a `Monoidal` `Profunctor` over `Mon`.
Together with `liftMon` and `hoistMon`, it characterizes the
free `Monoidal` `Profunctor`. -}
foldMon
  :: Monoidal q
  => (forall x y. p x y -> q x y)
  -> Mon p a b -> q a b
foldMon k = \case
  MonPure b -> pureP b
  MonAp f g x ->
    let
      h = foldMon k g
      y = lmap f (k x)
    in
      liftA2P ($) h y

instance Functor (Mon p a) where fmap = rmap
instance Applicative (Mon p a) where
  pure = pureP
  (<*>) = apP
instance Profunctor (Mon p) where
  dimap f g = \case
    MonPure b -> MonPure (g b)
    MonAp f' g' p -> MonAp (f' . f) (dimap f (g .) g') p
instance Monoidal (Mon p) where
  oneP = MonPure ()
  p0 >*< p1 = (,) <$> lmap fst p0 <*> lmap snd p1

{- | A free `Choice` and `Cochoice`, `Monoidal` `Profunctor` type. -}
newtype ChooseMon p a b =
  InChooseMon {outChooseMon :: ChooseMonF ChooseMon p a b}
  deriving newtype
    ( Functor
    , Filterable
    , Profunctor
    , Choice
    , Cochoice
    , ProfunctorFunctor
    )
instance Applicative (ChooseMon p a) where
  pure = InChooseMon . ChoosePure
  InChooseMon ChooseNil <*> _ = InChooseMon ChooseNil
  _ <*> InChooseMon ChooseNil = InChooseMon ChooseNil
  InChooseMon (ChoosePure f) <*> InChooseMon x = InChooseMon (f <$> x)
  InChooseMon f <*> InChooseMon (ChoosePure x) = InChooseMon (($ x) <$> f)
  InChooseMon (ChooseAp f g x) <*> y =
    let
      apply h a t = ($ a) <$> h t
    in
      InChooseMon (ChooseAp f (apply <$> g <*> y) x)
instance Monoidal (ChooseMon p)

{- | Folds functions to a `Choice` and `Cochoice`,
`Monoidal` `Profunctor` over `Mon`.
Together with `liftChooseMon` and `hoistChooseMon`,
it characterizes the free `Choice` and `Cochoice`,
`Monoidal` `Profunctor`. -}
foldChooseMon
  :: (Monoidal q, Choice q, Cochoice q)
  => (forall x y. p x y -> q x y)
  -> ChooseMon p a b
  -> q a b
foldChooseMon k = \case
  InChooseMon ChooseNil -> catMaybesP (pureP Nothing)
  InChooseMon (ChoosePure b) -> pureP b
  InChooseMon (ChooseAp f g x) ->
    let
      h = foldChooseMon k g
      y = dimapMaybe f Just (k x)
    in
      catMaybesP (liftA2P ($) h y)

{- | Lifts base terms to `ChooseMon`. -}
liftChooseMon :: p a b -> ChooseMon p a b
liftChooseMon = InChooseMon . ChooseAp Just (pure Just)

{- | Hoists base functions to `ChooseMon`. -}
hoistChooseMon
  :: (forall x y. p x y -> q x y)
  -> ChooseMon p a b -> ChooseMon q a b
hoistChooseMon h = \case
  InChooseMon ChooseNil -> InChooseMon ChooseNil
  InChooseMon (ChoosePure mb) -> InChooseMon (ChoosePure mb)
  InChooseMon (ChooseAp f (InChooseMon g) x) -> InChooseMon
    (ChooseAp f (hoistChooseMon h (InChooseMon g)) (h x))

{- | `ChooseMonF` is `ChooseMon` with its recursion abstracted
into a parameter, so it may be reused in
`Data.Profunctor.Distributor.ChooseDist`. -}
data ChooseMonF mon p a b where
  ChooseNil :: ChooseMonF mon p a b
  ChoosePure :: b -> ChooseMonF mon p a b
  ChooseAp
    :: (s -> Maybe a)
    -> mon p s (b -> Maybe t)
    -> p a b -> ChooseMonF mon p s t
instance (forall q. Profunctor (mon q))
  => Functor (ChooseMonF mon p a) where fmap = rmap
instance (forall q. Choice (mon q), forall q. Cochoice (mon q))
  => Filterable (ChooseMonF mon p a) where
    mapMaybe = mapMaybeP
instance (forall q. Profunctor (mon q))
  => Profunctor (ChooseMonF mon p) where
    dimap _ _ ChooseNil = ChooseNil
    dimap _ g (ChoosePure b) = ChoosePure (g b)
    dimap f' g' (ChooseAp f g x) =
      ChooseAp (f . f') (rmap (fmap g' .) (lmap f' g)) x
instance (forall q. Choice (mon q))
  => Choice (ChooseMonF mon p) where
    left' ChooseNil = ChooseNil
    left' (ChoosePure b) = ChoosePure (Left b)
    left' (ChooseAp f g x) =
      let
        apply e t = either ((Left <$>) . ($ t)) (Just . Right) e
      in
        ChooseAp (either f (pure Nothing)) (rmap apply (left' g)) x
    right' ChooseNil = ChooseNil
    right' (ChoosePure b) = ChoosePure (Right b)
    right' (ChooseAp f g x) =
      let
        apply e t = either (Just . Left) ((Right <$>) . ($ t)) e
      in
        ChooseAp (either (pure Nothing) f) (rmap apply (right' g)) x
instance (forall q. Cochoice (mon q))
  => Cochoice (ChooseMonF mon p) where
    unleft ChooseNil = ChooseNil
    unleft (ChoosePure (Left b)) = ChoosePure b
    unleft (ChoosePure (Right _)) = ChooseNil
    unleft (ChooseAp f g x) =
      let
        g' = rmap (Left . (either Just (pure Nothing) <=<)) g
      in
        ChooseAp (f . Left) (unleft g') x
    unright ChooseNil = ChooseNil
    unright (ChoosePure (Left _)) = ChooseNil
    unright (ChoosePure (Right b)) = ChoosePure b
    unright (ChooseAp f g x) =
      let
        g' = rmap (Right . (either (pure Nothing) Just <=<)) g
      in
        ChooseAp (f . Right) (unright g') x
instance ProfunctorFunctor mon => ProfunctorFunctor (ChooseMonF mon) where
  promap _ ChooseNil = ChooseNil
  promap _ (ChoosePure b) = ChoosePure b
  promap h (ChooseAp f g x) = ChooseAp f (promap h g) (h x)

{- | `WrappedMonoidal` can be used to derive instances from
a `Monoidal` `Profunctor` it wraps. -}
newtype WrappedMonoidal p a b = WrapMonoidal
  {unWrapMonoidal :: p a b}
instance Monoidal p => Functor (WrappedMonoidal p a) where
  fmap = rmap
instance Monoidal p => Applicative (WrappedMonoidal p a) where
  pure = pureP
  (<*>) = apP
deriving newtype instance Monoidal p
  => Profunctor (WrappedMonoidal p)
deriving newtype instance Monoidal p
  => Monoidal (WrappedMonoidal p)
deriving newtype instance (Monoidal p, Choice p)
  => Choice (WrappedMonoidal p)
deriving newtype instance (Monoidal p, Strong p)
  => Strong (WrappedMonoidal p)
instance (Monoidal p, Choice p, Strong p)
  => Traversing (WrappedMonoidal p) where
    wander f (WrapMonoidal p) = WrapMonoidal $
      dimap (f sell) extract (travBaz p) where
        travBaz :: p u v -> p (Bazaar (->) u w x) (Bazaar (->) v w x)
        travBaz q = eitherBazaar >$< right' (travBaz q >*< q)

newtype Shop a b s t = Shop
  {unShop :: Bazaar (->) (s -> a) b t}
  deriving newtype (Functor, Applicative)
instance Profunctor (Shop a b) where
  dimap f g (Shop baz) = Shop . fromFun $
    case toFun baz of
      FunPure c -> FunPure (g c)
      FunAp baz' h ->
        FunAp (unShop (dimap f (g .) (Shop baz'))) (h . f)
instance Monoidal (Shop a b)

runShop
  :: Monoidal p
  => Shop a b s t
  -> ((s -> a) -> p a b)
  -> p s t
runShop (Shop baz) f =
  unWrapMonoidal . runBazaar baz $ \sa ->
    lmap sa (WrapMonoidal (f sa))

{- | `FunList` is isomorphic to `Bazaar` @(->)@,
but modified so its nil and cons are pattern matchable. -}
data FunList a b t
  = FunPure t
  | FunAp (Bazaar (->) a b (b -> t)) a

instance Bizarre (->) FunList where
  bazaar f = bazaar f . fromFun

funList
  :: (t -> x)
  -> (Bazaar (->) a b (b -> t) -> a -> x)
  -> FunList a b t -> x
funList f g = \case
  FunPure t -> f t
  FunAp h a -> g h a

funListBazaar :: Iso
  (Bazaar (->) a1 b1 t1) (Bazaar (->) a2 b2 t2)
  (FunList a1 b1 t1) (FunList a2 b2 t2)
funListBazaar = iso toFun fromFun

eitherBazaar :: Iso
  (Bazaar (->) a1 b1 t1) (Bazaar (->) a2 b2 t2)
  (Either t1 (Bazaar (->) a1 b1 (b1 -> t1), a1))
  (Either t2 (Bazaar (->) a2 b2 (b2 -> t2), a2))
eitherBazaar = funListBazaar . dimap f (fmap g) where
  f = \case
    FunPure t -> Left t
    FunAp baz a -> Right (baz, a)
  g = \case
    Left t -> FunPure t
    Right (baz, a) -> FunAp baz a

toFun :: Bazaar (->) a b t -> FunList a b t
toFun (Bazaar f) = f sell

fromFun :: FunList a b t -> Bazaar (->) a b t
fromFun (FunPure t) = pure t
fromFun (FunAp f a) = ($) <$> f <*> sell a

instance Functor (FunList a b) where
  fmap f = funList (pure . f) (FunAp . fmap (f .))
instance Applicative (FunList a b) where
  pure = FunPure
  (<*>) = funList fmap $ \l x l' ->
    FunAp (flip <$> l <*> fromFun l') x
instance Sellable (->) FunList where sell = FunAp (pure id)

-- An indexed continuation monad
newtype Purchase a b s = Purchase {unPurchase :: (s -> a) -> b}

instance Functor (Purchase a b) where
  fmap sl (Purchase ab) = Purchase $ \la -> ab (la . sl)

instance a ~ b => Applicative (Purchase a b) where
  pure s = Purchase ($ s)
  Purchase slab <*> Purchase ab = Purchase $ \la -> slab $ \sl -> ab (la . sl)

buy :: Purchase a b a -> b
buy (Purchase f) = f id
