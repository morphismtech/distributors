{-|
Module      : Data.Profunctor.Monoidal
Description : monoidal and distributive profunctors
Copyright   : (c) Eitan Chatav, 2023
License     : LICENSE
Maintainer  : eitan.chatav@gmail.com
Stability   : experimental

-}
module Data.Profunctor.Monoidal
  ( -- * lax monoidal profunctors
    Monoidal (oneP, (>*<)), dimap2, (>*), (*<), (>:<)
  , pureP, apP, liftA2P, replicateP, replicateP', replicateP_, foreverP
  , Mon (MonPure, MonAp), liftMon
  , ChooseMon (ChoosePure, ChooseAp), liftChooseMon, foldChooseMon
    -- * traversal
  , wanderP, traverseP, traversalP
  ) where

import Control.Arrow
import Control.Comonad
import Control.Lens hiding (chosen, Traversing)
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
import Data.Profunctor.Yoneda
import Witherable

{- | A lax monoidal profunctor with respect to product
or simply a product profunctor
respects the monoidal structure given by
the nilary and binary products,
`()` and `(,)`.

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

{- | `dimap2` is a fully curried functionalization of `>*<`.
-}
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

(>*) :: Monoidal p => p () c -> p a b -> p a b
x >* y = dimap ((),) snd (x >*< y)
infixr 5 >*

(*<) :: Monoidal p => p a b -> p () c -> p a b
x *< y = dimap (,()) fst (x >*< y)
infixr 5 *<

(>:<) :: (Cons s t a b, Monoidal p, Choice p) => p a b -> p s t -> p s t
ab >:< st = _Cons >? ab >*< st
infixr 6 >:<

{- | `replicateP` is analagous to `replicateM`,
but slightly more general since it will output in
any `Stream`, not just lists.
-}
replicateP
  :: (Monoidal p, Choice p, Cochoice p, Stream s t a b)
  => Int -> p a b -> p s t
replicateP n _ | n <= 0 = _Null >?< oneP
replicateP n p = p >:< replicateP (n-1) p

replicateP'
  :: (Monoidal p, Choice p, SimpleStream s a)
  => Int -> p a a -> p s s
replicateP' n _ | n <= 0 = _Nil >? oneP
replicateP' n p = p >:< replicateP' (n-1) p

{- | `replicateP_` is like to `replicateM_`,
but with a `Monoidal` constraint.
-}
replicateP_ :: Monoidal p => Int -> p () c -> p a ()
replicateP_ n _ | n <= 0 = pureP ()
replicateP_ n p = p >* replicateP_ (n-1) p

foreverP :: Monoidal p => p () c -> p a b
foreverP p = let p' = p >* p' in p'

data Mon p a b where
  MonPure :: b -> Mon p a b
  MonAp
    :: (a -> s)
    -> Mon p a (t -> b)
    -> p s t
    -> Mon p a b
liftMon :: p a b -> Mon p a b
liftMon p = MonAp id (MonPure id) p
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

data ChooseMon p a b where
  ChoosePure :: Maybe b -> ChooseMon p a b
  ChooseAp
    :: (a -> Maybe s)
    -> ChooseMon p a (t -> Maybe b)
    -> p s t
    -> ChooseMon p a b
instance Functor (ChooseMon p a) where fmap = rmap
instance Filterable (ChooseMon p a) where
  mapMaybe = mapMaybeP
instance Applicative (ChooseMon p a) where
  pure = ChoosePure . Just
  ChoosePure Nothing <*> _ = ChoosePure Nothing
  ChoosePure (Just f) <*> x = f <$> x
  ChooseAp f g x <*> y =
    let
      apply h a t = ($ a) <$> h t
    in
      ChooseAp f (apply <$> g <*> y) x
instance Profunctor (ChooseMon p) where
  dimap _ g (ChoosePure b) = ChoosePure (g <$> b)
  dimap f' g' (ChooseAp f g x) =
    ChooseAp (f . f') ((fmap g' .) <$> lmap f' g) x
instance Monoidal (ChooseMon p)
instance Choice (ChooseMon p) where
  left' (ChoosePure b) = ChoosePure (Left <$> b)
  left' (ChooseAp f g x) =
    let
      apply e t = either ((Left <$>) . ($ t)) (Just . Right) e
    in
      ChooseAp (either f (pure Nothing)) (apply <$> (left' g)) x
  right' (ChoosePure b) = ChoosePure (Right <$> b)
  right' (ChooseAp f g x) =
    let
      apply e t = either (Just . Left) ((Right <$>) . ($ t)) e
    in
      ChooseAp (either (pure Nothing) f) (apply <$> (right' g)) x
instance Cochoice (ChooseMon p) where
  unleft (ChoosePure b) =
    ChoosePure (either Just (pure Nothing) =<< b)
  unleft (ChooseAp f g x) =
    let
      g' = (Left . (either Just (pure Nothing) <=<)) <$> g
    in
      ChooseAp (f . Left) (unleft g') x
  unright (ChoosePure b) =
    ChoosePure (either (pure Nothing) Just =<< b)
  unright (ChooseAp f g x) =
    let
      g' = (Right . (either (pure Nothing) Just <=<)) <$> g
    in
      ChooseAp (f . Right) (unright g') x
instance ProfunctorFunctor ChooseMon where
  promap _ (ChoosePure b) = ChoosePure b
  promap h (ChooseAp f g x) = ChooseAp f (promap h g) (h x)

foldChooseMon
  :: (Monoidal q, Choice q, Cochoice q)
  => (forall x y. p x y -> q x y)
  -> ChooseMon p a b
  -> q a b
foldChooseMon k = \case
  ChoosePure Nothing -> catMaybesP (pureP Nothing)
  ChoosePure (Just b) -> pureP b
  ChooseAp f g x ->
    let
      h = foldChooseMon k g
      y = dimapMaybe f Just (k x)
    in
      catMaybesP (liftA2P ($) h y)

liftChooseMon :: p a b -> ChooseMon p a b
liftChooseMon = ChooseAp Just (pure Just)

newtype FunList a b t = FunList {unFunList :: Either t (a, Bazaar (->) a b (b -> t))}

funList
  :: (t -> x)
  -> (a -> Bazaar (->) a b (b -> t) -> x)
  -> FunList a b t -> x
funList f g = either f (uncurry g) . unFunList

more :: a -> Bazaar (->) a b (b -> t) -> FunList a b t
more a t = FunList (Right (a,t))

toFun :: Bazaar (->) a b t -> FunList a b t
toFun (Bazaar f) = f sell

fromFun :: FunList a b t -> Bazaar (->) a b t
fromFun (FunList (Left t)) = pure t
fromFun (FunList (Right (a, b))) = ($) <$> b <*> sell a

instance Functor (FunList a b) where
  fmap f = funList (pure . f) (\x l -> more x (fmap (f .) l))
instance Applicative (FunList a b) where
  pure = FunList . Left
  (<*>) = funList fmap (\x l l' -> more x (flip <$> l <*> fromFun l'))
instance Sellable (->) FunList where sell a = more a (pure id)

traversalP
  :: (forall p. (Choice p, Strong p, Monoidal p) => p a b -> p s t)
  -> Traversal s t a b
traversalP abst = runStar . abst . Star

wanderP :: (Choice p, Strong p, Monoidal p) => ATraversal s t a b -> p a b -> p s t
wanderP f =
  let
    traverseFun
      :: (Choice q, Strong q, Monoidal q)
      => q u v -> q (Bazaar (->) u w x) (Bazaar (->) v w x)
    traverseFun k = dimap
      (unFunList . toFun)
      (fromFun . FunList)
      (right' (k >*< traverseFun k))
  in
    dimap (f sell) extract . traverseFun

traverseP :: (Choice p, Strong p, Monoidal p, Traversable f) => p a b -> p (f a) (f b)
traverseP = wanderP traverse
