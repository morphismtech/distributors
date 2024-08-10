{-|
Module      : Data.Profunctor.Distributor
Description : monoidal and distributive profunctors
Copyright   : (c) Eitan Chatav, 2024
License     : LICENSE
Maintainer  : eitan.chatav@gmail.com
Stability   : experimental

-}
module Data.Profunctor.Distributor
  ( -- * Lax Distributive Profunctors
    Distributor (zeroP, (>+<), several, severalPlus, possibly)
  , emptyP
  , dialt
  , altP
    -- * Free Distributive Profunctors
  , Dist (DistEmpty, DistEither)
  , liftDist
  , hoistDist
  , foldDist
  , DistAlt (DistAlts)
  , liftDistAlt
  , several1
    -- * Separate
  , Separate (by, beginBy, endBy)
  , sep
  , atLeast0
  , moreThan0
  , atLeast1
    -- * pattern matching
  , eot, onCase, onCocase
  , dichainl, dichainr, dichainl', dichainr'
  ) where

import Control.Applicative hiding (WrappedArrow(..))
import Control.Applicative.Free
import Control.Arrow
import Control.Lens hiding (chosen, Traversing)
import Control.Lens.PartialIso
import Control.Lens.Stream
import Data.Bifunctor.Biff
import Data.Bifunctor.Clown
import Data.Bifunctor.Joker
import Data.Bifunctor.Product
import Data.Bifunctor.Tannen
import Data.Functor.Adjunction (Adjunction, unabsurdL, cozipL)
import Data.Functor.Contravariant.Divisible hiding (chosen)
import qualified Data.Functor.Contravariant.Divisible as Con (chosen)
import Data.Profunctor hiding (WrappedArrow(..))
import qualified Data.Profunctor as Pro (WrappedArrow(..))
import Data.Profunctor.Cayley
import Data.Profunctor.Composition
import Data.Profunctor.Monad
import Data.Profunctor.Monoidal
import Data.Profunctor.Yoneda
import Data.Void
import Generics.Eot
import Witherable

import Data.Kind

{- | A `Distributor`, or lax distributive profunctor,
respects distributive category structure,
that is nilary and binary products and coproducts,
@()@, @(,)@, `Void` and `Either`.

In addition to the product laws for `Monoidal`, we have
sum laws for `Distributor`.

Laws:

>>> :{
let f |+| g = either (Left . f) (Right . g)
    lunit = dimap (either absurd id) Right
    runit = dimap (either id absurd) Left
    assoc = dimap
      (either (Left . Left) (either (Left . Right) Right))
      (either (either Left (Right . Left)) (Right . Right))
:}
prop> dimap (f |+| g) (h |+| i) (p >+< q) = dimap f h p >+< dimap g i q
prop> zeroP >+< p = lunit p
prop> p >+< zeroP = runit p
prop> p >+< q >+< r = assoc ((p >+< q) >+< r)

`Distributor` is not equivalent to an `Alternative` `Profunctor`.
However, when the `Profunctor` is `Choice` and `Cochoice`, then
`Alternative` gives a default implementation for `Distributor`.
-}
class Monoidal p => Distributor p where

  {- |
  `zeroP` is a symmetric analog of `emptyP`.
  For an `Alternative` `Distributor`,

  prop> zeroP = empty
  -}
  zeroP :: p Void Void
  default zeroP :: (forall x. Alternative (p x)) => p Void Void
  zeroP = empty

  {- |
  `>+<` is a symmetrical analog of `dialt`.
  For an `Alternative` `Distributor` which is `Choice` and `Cochoice`,

  prop> p >+< q = alternate (Left p) <|> alternate (Right q)
  -}
  (>+<) :: p a b -> p c d -> p (Either a c) (Either b d)
  default (>+<)
    :: (Choice p, Cochoice p, forall x. Alternative (p x))
    => p a b -> p c d -> p (Either a c) (Either b d)
  p >+< q = alternate (Left p) <|> alternate (Right q)
  infixr 1 >+<

  {- |
  `several` is the Kleene star operator, of zero or more times.
  -}
  several :: (SimpleStream s a, SimpleStream t b) => p a b -> p s t
  several p = apIso _Stream $ oneP >+< severalPlus p

  {- |
  `severalPlus` is the Kleene plus operator, of one or more times.
  -}
  severalPlus
    :: (SimpleStream s a, SimpleStream t b)
    => p a b -> p (a,s) (b,t)
  severalPlus p = p >*< several p

  {- |
  `possibly` is zero or one times.
  -}
  possibly :: p a b -> p (Maybe a) (Maybe b)
  possibly p = apIso _M2E $ oneP >+< p

apIso :: Profunctor p => AnIso s t a b -> p a b -> p s t
apIso i p = withIso i $ \here there -> dimap here there p

{- | Like `severalPlus`, but conses the `Stream` type. -}
several1
  :: (Choice p, Distributor p, Stream s t a b)
  => p a b -> p s t
several1 p = _Cons >? severalPlus p

{- | At least zero operator with a separator. -}
atLeast0
  :: (Distributor p, Stream s t a b)
  => p a b -> Separate p -> p s t
atLeast0 p (Separate separator beg end) =
  beg >* apIso _Stream (oneP >+< p `sepBy` separator) *< end

{- | More than zero operator with a separator. -}
moreThan0
  :: (Distributor p, Stream s t a b)
  => p a b -> Separate p -> p (a,s) (b,t)
moreThan0 p (Separate separator beg end) =
  beg >* p `sepBy` separator *< end

{- | Like `moreThan0`, but conses the `Stream` type. -}
atLeast1
  :: (Distributor p, Choice p, Stream s t a b)
  => p a b -> Separate p -> p s t
atLeast1 p s = _Cons >? moreThan0 p s

sepBy
  :: (Distributor p, Stream s t a b)
  => p a b -> p () () -> p (a,s) (b,t)
sepBy p separator = p >*< several (separator >* p)

{- | Used to parse multiple times, delimited `by` a separator,
a `beginBy`, and an `endBy`. -}
data Separate p = Separate
  { by :: p () ()
  , beginBy :: p () ()
  , endBy :: p () ()
  }

{- | A default `Separate` which can be modified by updating `by`,
`beginBy`, or `endBy` fields -}
sep :: Monoidal p => Separate p
sep = Separate oneP oneP oneP

instance Distributor (->) where
  zeroP = id
  (>+<) = (+++)
instance Monoid s => Distributor (Forget s) where
  zeroP = Forget absurd
  Forget kL >+< Forget kR = Forget (either kL kR)
instance Decidable f => Distributor (Clown f) where
  zeroP = Clown lost
  Clown x >+< Clown y = Clown (Con.chosen x y)
instance Alternative g => Distributor (Joker g) where
  zeroP = Joker empty
  Joker x >+< Joker y = Joker (Left <$> x <|> Right <$> y)
instance Applicative f => Distributor (Star f) where
  zeroP = Star absurd
  Star f >+< Star g =
    Star (either (fmap Left . f) (fmap Right . g))
deriving via (Star m) instance Monad m => Distributor (Kleisli m)
instance Adjunction f u => Distributor (Costar f) where
  zeroP = Costar unabsurdL
  Costar f >+< Costar g = Costar (bimap f g . cozipL)
instance (Applicative f, Distributor p)
  => Distributor (Tannen f p) where
    zeroP = Tannen (pure zeroP)
    Tannen x >+< Tannen y = Tannen ((>+<) <$> x <*> y)
instance (Applicative f, Distributor p)
  => Distributor (Cayley f p) where
    zeroP = Cayley (pure zeroP)
    Cayley x >+< Cayley y = Cayley ((>+<) <$> x <*> y)
instance (Adjunction f u, Applicative g, Distributor p)
  => Distributor (Biff p f g) where
    zeroP = Biff (dimap unabsurdL absurd zeroP)
    Biff x >+< Biff y = Biff $ dimap
      cozipL
      (either (Left <$>) (Right <$>))
      (x >+< y)
instance (ArrowZero p, ArrowChoice p)
  => Distributor (Pro.WrappedArrow p) where
    zeroP = zeroArrow
    (>+<) = (+++)
instance (Distributor p, Distributor q)
  => Distributor (Procompose p q) where
    zeroP = Procompose zeroP zeroP
    Procompose xL yL >+< Procompose xR yR =
      Procompose (xL >+< xR) (yL >+< yR)
instance (Distributor p, Distributor q)
  => Distributor (Product p q) where
    zeroP = Pair zeroP zeroP
    Pair x0 y0 >+< Pair x1 y1 = Pair (x0 >+< x1) (y0 >+< y1)
instance Monoid s => Distributor (PartialExchange s t)
instance Distributor p => Distributor (Yoneda p) where
  zeroP = proreturn zeroP
  ab >+< cd = proreturn (proextract ab >+< proextract cd)
instance Distributor p => Distributor (Coyoneda p) where
  zeroP = proreturn zeroP
  ab >+< cd = proreturn (proextract ab >+< proextract cd)

{- | The `Distributor` version of `empty`,
`emptyP` is a functionalization of `zeroP`.
-}
emptyP
  :: Distributor p
  => (a -> Void) -> p a b
emptyP f = dimap f absurd zeroP

{- | `dialt` is a fully curried functionalization of `>+<`. -}
dialt
  :: Distributor p
  => (s -> Either a c)
  -> (b -> t)
  -> (d -> t)
  -> p a b -> p c d -> p s t
dialt f g h p q = dimap f (either g h) (p >+< q)

{- | `altP` is the `Distributor` version of `(<|>)`. -}
altP
  :: Distributor p
  => (s -> Either a c) -> p a t -> p c t -> p s t
altP f = dialt f id id

{- | A free `Distributor` type, parametrized by
a choice of free `Applicative`. -}
type Dist :: ((Type -> Type) -> (Type -> Type)) -> (Type -> Type -> Type) -> Type -> Type -> Type
data Dist ap p a b where
  DistEmpty 
    :: (a -> Void)
    -> Dist ap p a b
  DistEither
    :: (a -> Either s c)
    -> ap (p s) b
    -> Dist ap p c b
    -> Dist ap p a b

{- | Composed with @liftAp@, `liftDist` lifts base terms to `Dist`. -}
liftDist :: ap (p a) b -> Dist ap p a b
liftDist x = DistEither Left x (DistEmpty id)

{- | Composed with @hoistAp@, `hoistDist` hoists base functions to `Dist`. -}
hoistDist
  :: (forall x y. ap (p x) y -> ap (q x) y)
  -> Dist ap p a b -> Dist ap q a b
hoistDist h = \case
  DistEmpty f -> DistEmpty f
  DistEither f b x -> DistEither f (h b) (hoistDist h x)

{- | Folds functions to a `Distributor` over `Dist`.
Together with `liftDist` and `hoistDist`, it characterizes the
free `Distributor`. -}
foldDist
  :: (Distributor q, forall x. Applicative (q x))
  => (forall x y. p x y -> q x y)
  -> Dist Ap p a b -> q a b
foldDist k = \case
  DistEmpty f ->
    emptyP f
  DistEither f b x ->
    altP f (runAp k b) (foldDist k x)

instance (forall f. Functor (ap f))
  => Functor (Dist ap p a) where fmap = rmap
instance (forall f. Applicative (ap f))
  => Applicative (Dist ap p a) where
  pure b = liftDist (pure b)
  -- 0*x=0
  liftA2 _ (DistEmpty absurdum) _ = DistEmpty absurdum
  -- (x+y)*z=x*z+y*z
  liftA2 g (DistEither f x y) z =
    let
      ff a = bimap (,a) (,a) (f a)
    in
      altP ff
        (uncurry g <$> (liftDist x >*< z))
        (uncurry g <$> (y >*< z))
instance (forall f. Functor (ap f))
  => Profunctor (Dist ap p) where
  dimap f _ (DistEmpty absurdum) = DistEmpty (absurdum . f)
  dimap f' g' (DistEither f x y) =
    DistEither (f . f') (g' <$> x) (g' <$> y)
instance (forall f. Applicative (ap f)) => Monoidal (Dist ap p)
instance (forall f. Applicative (ap f))
  => Distributor (Dist ap p) where
  zeroP = DistEmpty absurd
  -- 0+x=x
  DistEmpty absurdum >+< x =
    dimap (either (absurd . absurdum) id) Right x
  -- (x+y)+z=x+(y+z)
  DistEither f x y >+< z =
    let
      assocE (Left (Left a)) = Left a
      assocE (Left (Right b)) = Right (Left b)
      assocE (Right c) = Right (Right c)
      f' = assocE . either (Left . f) Right
    in
      dialt f' Left id (liftDist x) (y >+< z)
instance (forall f. Filterable (ap f)) => Filterable (Dist ap p x) where
  catMaybes (DistEmpty absurdum) = DistEmpty absurdum
  catMaybes (DistEither f x y) = DistEither f (catMaybes x) (catMaybes y)
instance (forall f. Filterable (ap f)) => Cochoice (Dist ap p) where
  unleft (DistEmpty absurdum) = DistEmpty (absurdum . Left)
  unleft (DistEither f x y) =
    DistEither (f . Left)
      (mapMaybe (either Just (const Nothing)) x)
      (mapMaybe (either Just (const Nothing)) y)
  unright (DistEmpty absurdum) = DistEmpty (absurdum . Right)
  unright (DistEither f x y) =
    DistEither (f . Right)
      (mapMaybe (either (const Nothing) Just) x)
      (mapMaybe (either (const Nothing) Just) y)


{- | A free `Distributor` type, generated over
a `Choice` and `Cochoice`, `Applicative` `Profunctor`. -}
newtype DistAlt p a b = DistAlts [p a b]
instance (forall x. Functor (p x)) => Functor (DistAlt p a) where
  fmap f (DistAlts alts) = DistAlts (map (fmap f) alts)
instance (forall x. Applicative (p x))
  => Applicative (DistAlt p a) where
  pure b = liftDistAlt (pure b)
  DistAlts xs <*> DistAlts ys =
    DistAlts [x <*> y | x <- xs, y <- ys]
instance (forall x. Applicative (p x))
  => Alternative (DistAlt p a) where
    empty = DistAlts []
    DistAlts altsL <|> DistAlts altsR = DistAlts (altsL ++ altsR)
instance Profunctor p => Profunctor (DistAlt p) where
  dimap f g (DistAlts alts) = DistAlts (map (dimap f g) alts)
instance (forall x. Applicative (p x), Profunctor p)
  => Monoidal (DistAlt p)
instance Choice p => Choice (DistAlt p) where
  left' (DistAlts alts) = DistAlts (map left' alts)
  right' (DistAlts alts) = DistAlts (map right' alts)
instance Cochoice p => Cochoice (DistAlt p) where
  unleft (DistAlts alts) = DistAlts (map unleft alts)
  unright (DistAlts alts) = DistAlts (map unright alts)
instance (Choice p, Cochoice p, forall x. Applicative (p x))
  => Distributor (DistAlt p)

liftDistAlt :: p a b -> DistAlt p a b
liftDistAlt p = DistAlts [p]

-- positional pattern matching
eot
  :: (HasEot a, HasEot b, Profunctor p)
  => p (Eot a) (Eot b) -> p a b
eot = dimap toEot fromEot

-- exhaustive pattern matching
onCase
  :: (Distributor p, Choice p)
  => APrism s t a b
  -> p a b
  -> p c Void
  -> p s t
onCase p p1 p0 = dialt Right absurd id p0 (p >? p1)

-- exhaustive copattern matching
onCocase
  :: (Distributor p, Cochoice p)
  => APrism b a t s
  -> p a b
  -> p c Void
  -> p s t
onCocase p p1 p0 = dialt Right absurd id p0 (p ?< p1)

dichainl
  :: forall p a b. (Choice p, Cochoice p, Distributor p)
  => APartialIso a b (a,a) (b,b)
  -> p () ()
  -> p a b
  -> p a b
dichainl i opr arg =
  let
    conj = coPartialIso . difoldl . coPartialIso
    sev = several @p @[a]
  in
    conj i >?< arg >*< sev (opr >* arg)

dichainl'
  :: forall p a. (Cochoice p, Distributor p)
  => APrism' (a,a) a
  -> p () ()
  -> p a a
  -> p a a
dichainl' p opr arg =
  let
    sev = several @p @[a]
  in
    difoldl' p ?< arg >*< sev (opr >* arg)

dichainr
  :: forall p a b. (Choice p, Cochoice p, Distributor p)
  => APartialIso a b (a,a) (b,b)
  -> p () ()
  -> p a b
  -> p a b
dichainr i opr arg =
  let
    conj = coPartialIso . difoldr . coPartialIso
    sev = several @p @[a]
  in
    conj i >?< sev (opr >* arg) >*< arg

dichainr'
  :: forall p a. (Cochoice p, Distributor p)
  => APrism' (a,a) a
  -> p () ()
  -> p a a
  -> p a a
dichainr' p opr arg =
  let
    sev = several @p @[a]
  in
    difoldr' p ?< sev (opr >* arg) >*< arg 
