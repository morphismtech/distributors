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
  , meander
    -- * Free Monoidal Profunctors
  , Mon (..)
  , foldMon
  , ChooseMon (..)
  , foldChooseMon
  , ChooseMonF (..)
    -- * Monoidal types
  , WrappedMonoidal (..)
  ) where

import Control.Arrow
import Control.Comonad
import Control.Lens hiding (chosen, Traversing)
import Control.Lens.Internal.Context
import Control.Lens.Internal.FunList
import Control.Lens.Internal.Profunctor
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
import Data.Profunctor.Choose
import Data.Profunctor.Composition
import Data.Profunctor.Monad
import Data.Profunctor.Traversing
import Data.Profunctor.Yoneda
import Data.Quiver.Functor
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
instance Monoidal (Shop a b)
instance (Monoidal p, Applicative f)
  => Monoidal (WrappedPafb f p) where
    oneP = WrapPafb (pureP (pure ()))
    WrapPafb ab >*< WrapPafb cd =
      WrapPafb (dimap2 fst snd (liftA2 (,)) ab cd)

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
  :: (Monoidal p, Choice p, Cochoice p, Stream s t a b, Cons s t a b)
  => Int -> p a b -> p s t
replicateP n _ | n <= 0 = _Null >?< oneP
replicateP n p = p >:< replicateP (n-1) p

{- | `replicateP'` is a simple analog to `replicateM`. -}
replicateP'
  :: (Monoidal p, Choice p, Stream' s a)
  => Int -> p a a -> p s s
replicateP' n _ | n <= 0 = _Empty >? oneP
replicateP' n p = p >:< replicateP' (n-1) p

{- | `replicateP_` is like `replicateM_`. -}
replicateP_ :: Monoidal p => Int -> p () c -> p a ()
replicateP_ n _ | n <= 0 = pureP ()
replicateP_ n p = p >* replicateP_ (n-1) p

{- | `foreverP` is like `forever`. -}
foreverP :: Monoidal p => p () c -> p a b
foreverP p = let p' = p >* p' in p'

{- | `meander` exhibits the implicit `Traversing` 
structure of a `Choice`, `Strong` `Monoidal`. -}
meander
  :: (Choice p, Strong p, Monoidal p)
  => ATraversal s t a b -> p a b -> p s t
meander trav
  = unWrapMonoidal
  . wander (cloneTraversal trav)
  . WrapMonoidal

{- | A free `Monoidal` `Profunctor` type. -}
data Mon p a b where
  MonPure :: b -> Mon p a b
  MonAp
    :: (s -> a)
    -> Mon p s (b -> t)
    -> p a b
    -> Mon p s t

instance QFunctor Mon where
  qmap h = \case
    MonPure b -> MonPure b
    MonAp f g x -> MonAp f (qmap h g) (h x)

instance QPointed Mon where
  qsingle p = MonAp id (MonPure id) p

instance QMonad Mon where
  qjoin = foldMon id

{- | Fold to a `Monoidal` `Profunctor` over `Mon`.-}
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
    , QFunctor
    , QPointed
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
instance QMonad ChooseMon where
  qjoin = foldChooseMon id

{- | Run `ChooseMon` in any `Choice`, `Cochoice`, `Monoidal`. -}
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
instance QFunctor mon => QFunctor (ChooseMonF mon) where
  qmap _ ChooseNil = ChooseNil
  qmap _ (ChoosePure b) = ChoosePure b
  qmap h (ChooseAp f g x) = ChooseAp f (qmap h g) (h x)
instance
  ( QFunctor mon
  , forall q. Monoidal (mon q)
  ) => QPointed (ChooseMonF mon) where
    qsingle = ChooseAp Just (pureP Just)

{- | `WrappedMonoidal` can be used to derive instances from
a `Monoidal` `Profunctor` it wraps. -}
newtype WrappedMonoidal p a b = WrapMonoidal
  {unWrapMonoidal :: p a b}
instance Monoidal p => Functor (WrappedMonoidal p a) where
  fmap = rmap
instance Monoidal p => Applicative (WrappedMonoidal p a) where
  pure = pureP
  (<*>) = apP
deriving newtype instance (Monoidal p, forall x. Filterable (p x))
  => Filterable (WrappedMonoidal p a)
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
        travBaz q = mapIso _Bazaar $ right' (q >*< travBaz q)
