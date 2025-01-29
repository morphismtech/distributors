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
  , PartialMon (..)
  , foldPartialMon
  , PartialMonF (..)
    -- * Wrapped types
  , WrappedMonoidal (..)
  , WrappedApplicator (..)
  ) where

import Control.Applicative
import Control.Arrow
import Control.Comonad
import Control.Lens hiding (chosen, Traversing)
import Control.Lens.Internal.Context
import Control.Lens.Internal.FunList
import Control.Lens.Internal.Prism
import Control.Lens.Internal.Profunctor
import Control.Lens.PartialIso
import Control.Lens.Stream
import Control.Monad
import Data.Bifunctor.Biff
import Data.Bifunctor.Clown
import Data.Bifunctor.Joker
import Data.Bifunctor.Product
import Data.Bifunctor.Tannen
import Data.Distributive
import Data.Functor.Contravariant.Divisible hiding (chosen)
import Data.Profunctor hiding (WrappedArrow(..))
import qualified Data.Profunctor as Pro (WrappedArrow(..))
import Data.Profunctor.Cayley
import Data.Profunctor.Partial
import Data.Profunctor.Composition
import Data.Profunctor.Monad
import Data.Profunctor.Traversing
import Data.Profunctor.Yoneda
import Data.Quiver.Functor
import Data.Tagged
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
instance Monoidal p => Monoidal (Yoneda p) where
  oneP = proreturn oneP
  ab >*< cd = proreturn (proextract ab >*< proextract cd)
instance Monoidal p => Monoidal (Coyoneda p) where
  oneP = proreturn oneP
  ab >*< cd = proreturn (proextract ab >*< proextract cd)
instance Monoidal (SpiceShop a b)
instance (Monoidal p, Applicative f)
  => Monoidal (WrappedPafb f p) where
    oneP = WrapPafb (pureP (pure ()))
    WrapPafb ab >*< WrapPafb cd =
      WrapPafb (dimap2 fst snd (liftA2 (,)) ab cd)
instance Monoidal (Grating a b)
instance Monoidal (PoshSpice a b)
instance Monoidal Tagged

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
newtype PartialMon p a b =
  InPartialMon {outPartialMon :: PartialMonF PartialMon p a b}
  deriving newtype
    ( Functor
    , Filterable
    , Profunctor
    , Choice
    , Cochoice
    , QFunctor
    , QPointed
    )
instance Applicative (PartialMon p a) where
  pure = InPartialMon . PartialPure
  InPartialMon PartialNil <*> _ = InPartialMon PartialNil
  _ <*> InPartialMon PartialNil = InPartialMon PartialNil
  InPartialMon (PartialPure f) <*> InPartialMon x = InPartialMon (f <$> x)
  InPartialMon f <*> InPartialMon (PartialPure x) = InPartialMon (($ x) <$> f)
  InPartialMon (PartialAp f g x) <*> y =
    let
      apply h a t = ($ a) <$> h t
    in
      InPartialMon (PartialAp f (apply <$> g <*> y) x)
instance Monoidal (PartialMon p)
instance QMonad PartialMon where
  qjoin = foldPartialMon id

{- | Run `PartialMon` in any `Choice`, `Cochoice`, `Monoidal`. -}
foldPartialMon
  :: (Monoidal q, Choice q, Cochoice q)
  => (forall x y. p x y -> q x y)
  -> PartialMon p a b
  -> q a b
foldPartialMon k = \case
  InPartialMon PartialNil -> catMaybesP (pureP Nothing)
  InPartialMon (PartialPure b) -> pureP b
  InPartialMon (PartialAp f g x) ->
    let
      h = foldPartialMon k g
      y = dimapMaybe f Just (k x)
    in
      catMaybesP (liftA2P ($) h y)

{- | `PartialMonF` is `PartialMon` with its recursion abstracted
into a parameter, so it may be reused in
`Data.Profunctor.Distributor.PartialDist`. -}
data PartialMonF mon p a b where
  PartialNil :: PartialMonF mon p a b
  PartialPure :: b -> PartialMonF mon p a b
  PartialAp
    :: (s -> Maybe a)
    -> mon p s (b -> Maybe t)
    -> p a b -> PartialMonF mon p s t
instance (forall q. Profunctor (mon q))
  => Functor (PartialMonF mon p a) where fmap = rmap
instance (forall q. Choice (mon q), forall q. Cochoice (mon q))
  => Filterable (PartialMonF mon p a) where
    mapMaybe = mapMaybeP
instance (forall q. Profunctor (mon q))
  => Profunctor (PartialMonF mon p) where
    dimap _ _ PartialNil = PartialNil
    dimap _ g (PartialPure b) = PartialPure (g b)
    dimap f' g' (PartialAp f g x) =
      PartialAp (f . f') (rmap (fmap g' .) (lmap f' g)) x
instance (forall q. Choice (mon q))
  => Choice (PartialMonF mon p) where
    left' PartialNil = PartialNil
    left' (PartialPure b) = PartialPure (Left b)
    left' (PartialAp f g x) =
      let
        apply e t = either ((Left <$>) . ($ t)) (Just . Right) e
      in
        PartialAp (either f (pure Nothing)) (rmap apply (left' g)) x
    right' PartialNil = PartialNil
    right' (PartialPure b) = PartialPure (Right b)
    right' (PartialAp f g x) =
      let
        apply e t = either (Just . Left) ((Right <$>) . ($ t)) e
      in
        PartialAp (either (pure Nothing) f) (rmap apply (right' g)) x
instance (forall q. Cochoice (mon q))
  => Cochoice (PartialMonF mon p) where
    unleft PartialNil = PartialNil
    unleft (PartialPure (Left b)) = PartialPure b
    unleft (PartialPure (Right _)) = PartialNil
    unleft (PartialAp f g x) =
      let
        g' = rmap (Left . (either Just (pure Nothing) <=<)) g
      in
        PartialAp (f . Left) (unleft g') x
    unright PartialNil = PartialNil
    unright (PartialPure (Left _)) = PartialNil
    unright (PartialPure (Right b)) = PartialPure b
    unright (PartialAp f g x) =
      let
        g' = rmap (Right . (either (pure Nothing) Just <=<)) g
      in
        PartialAp (f . Right) (unright g') x
instance QFunctor mon => QFunctor (PartialMonF mon) where
  qmap _ PartialNil = PartialNil
  qmap _ (PartialPure b) = PartialPure b
  qmap h (PartialAp f g x) = PartialAp f (qmap h g) (h x)
instance
  ( QFunctor mon
  , forall q. Monoidal (mon q)
  ) => QPointed (PartialMonF mon) where
    qsingle = PartialAp Just (pureP Just)

{- | `WrappedMonoidal` can be used to derive instances from
a `Monoidal` `Profunctor` it wraps. -}
newtype WrappedMonoidal p a b = WrapMonoidal
  {unWrapMonoidal :: p a b}
instance Profunctor p => Functor (WrappedMonoidal p a) where
  fmap = rmap
instance Monoidal p => Applicative (WrappedMonoidal p a) where
  pure = pureP
  (<*>) = apP
deriving newtype instance (Monoidal p, forall x. Filterable (p x))
  => Filterable (WrappedMonoidal p a)
deriving newtype instance Profunctor p
  => Profunctor (WrappedMonoidal p)
deriving newtype instance Closed p
  => Closed (WrappedMonoidal p)
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

newtype WrappedApplicator p a b = WrapApplicator
  {unWrapApplicator :: p a b}
    deriving newtype
      ( Functor
      , Applicative
      , Alternative
      , Filterable
      , Profunctor
      , Choice
      )
instance (forall x. Distributive (p x))
  => Distributive (WrappedApplicator p a) where
    distribute = WrapApplicator . distribute . fmap unWrapApplicator
instance (Profunctor p, forall x. Applicative (p x))
  => Monoidal (WrappedApplicator p)
instance (Profunctor p, forall x. Distributive (p x))
  => Closed (WrappedApplicator p) where
    closed (WrapApplicator p) = WrapApplicator $
      distribute (flip (lmap . (&)) p)
instance (Profunctor p, forall x. Filterable (p x))
  => Cochoice (WrappedApplicator p) where
    unleft = catMaybes . dimap Left (either Just (const Nothing))
    unright = catMaybes . dimap Right (either (const Nothing) Just)
instance
  ( Applicative f
  , forall x. Applicative (p x)
  , Profunctor p
  ) => Monoidal (Pafb f p)

instance Monoidal (Market a b)

-- questionable instance
-- instance Monoidal (Market a b) where
--   oneP = Market (const ()) Left
--   Market f0 g0 >*< Market f1 g1 = Market (f0 &&& f1) $ \(a0,a1) ->
--     case (g0 a0, g1 a1) of
--       (Left b0, Left b1) -> Left (b0,b1)
--       (Right c, _) -> Right c
--       (Left _, Right c) -> Right c

-- instance (Closed p, Distributive f) 
--   => Closed (WrappedApplicator (WrappedPafb f p)) where
--     closed (WrapApplicator (WrapPafb p))
--       = WrapApplicator . WrapPafb $ rmap distribute (closed p)

-- instance (Closed p, Functor f, Distributive g)
--   => Closed (WrappedApplicator (Biff p f g)) where
--     closed (WrapApplicator (Biff p))
--       = WrapApplicator . Biff
--       $ dimap ((>>>) (&) . (<&>)) distribute (closed p)

-- instance (Cochoice p, Filterable f) 
--   => Cochoice (WrappedPafb f p) where
--     unleft (WrapPafb pf) = WrapPafb $
--       unleft (rmap (Left . mapMaybe (either Just (const Nothing))) pf)
--     unright (WrapPafb pf) = WrapPafb $
--       unright (rmap (Right . mapMaybe (either (const Nothing) Just)) pf)
