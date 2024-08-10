{-|
Module      : Data.Profunctor.Distributor
Description : lax distributive profunctors
Copyright   : (c) Eitan Chatav, 2024
License     : LICENSE
Maintainer  : eitan.chatav@gmail.com
Stability   : experimental

-}
module Data.Profunctor.Distributor
  ( -- * Lax Distributive Profunctors
    Distributor (..)
  , emptyP
  , dialt
  , altP
  , several1
  , atLeast0
  , moreThan0
  , atLeast1
    -- * Free Distributive Profunctors
  , Dist (..)
  , liftDist
  , hoistDist
  , foldDistWith
  , ChooseDist (..)
  , liftChooseDist
  , hoistChooseDist
    -- * Separate
  , Separate (..)
  , sep
    -- * pattern matching
  , eot, onCase, onCocase
  , dichainl, dichainr, dichainl', dichainr'
  ) where

import Control.Applicative hiding (WrappedArrow(..))
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
import Data.Kind
import Data.Profunctor.Monad
import Data.Profunctor.Monoidal
import Data.Profunctor.Yoneda
import Data.Void
import Generics.Eot
import Witherable

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

{- | A free `Distributor` type over an unconstrained quiver,
parametrized by a choice of free `Applicative`. -}
type Dist
  :: ((Type -> Type) -> (Type -> Type))
     -- ^ choice of free `Applicative`
  -> (Type -> Type -> Type)
     -- ^ base quiver
  -> Type -> Type -> Type
data Dist ap p a b where
  DistNil 
    :: (a -> Void)
    -> Dist ap p a b
  DistEither
    :: (a -> Either s c)
    -> ap (p s) b
    -> Dist ap p c b
    -> Dist ap p a b

{- | `liftDist` `.` @liftAp@ lifts base terms to `Dist`. -}
liftDist :: ap (p a) b -> Dist ap p a b
liftDist x = DistEither Left x (DistNil id)

{- | `hoistDist` `.` @hoistAp@ hoists base functions to `Dist`. -}
hoistDist
  :: (forall x y. ap (p x) y -> ap (q x) y)
  -> Dist ap p a b -> Dist ap q a b
hoistDist h = \case
  DistNil f -> DistNil f
  DistEither f b x -> DistEither f (h b) (hoistDist h x)

{- |
`foldDistWith` @runAp@ folds functions to a
`Distributor` over `Dist` @Ap@.
Together with `liftDist` and `hoistDist`,
`foldDistWith` characterizes the free `Distributor`.
-}
foldDistWith
  :: ( Distributor q
     , forall x. Applicative (q x)
     )
  => (forall s t. (forall x y. p x y -> q x y) -> ap (p s) t -> q s t)
     -- ^ use the @runAp@ fold-function of the free `Applicative` @ap@
  -> (forall x y. p x y -> q x y)
  -> Dist ap p a b -> q a b
foldDistWith foldAp k = \case
  DistNil f ->
    emptyP f
  DistEither f b x ->
    altP f (foldAp k b) (foldDistWith foldAp k x)

instance (forall f. Functor (ap f))
  => Functor (Dist ap p a) where fmap = rmap
instance (forall f. Applicative (ap f))
  => Applicative (Dist ap p a) where
  pure b = liftDist (pure b)
  -- 0*x=0
  liftA2 _ (DistNil absurdum) _ = DistNil absurdum
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
  dimap f _ (DistNil absurdum) = DistNil (absurdum . f)
  dimap f' g' (DistEither f x y) =
    DistEither (f . f') (g' <$> x) (g' <$> y)
instance (forall f. Applicative (ap f)) => Monoidal (Dist ap p)
instance (forall f. Applicative (ap f))
  => Distributor (Dist ap p) where
  zeroP = DistNil absurd
  -- 0+x=x
  DistNil absurdum >+< x =
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
  catMaybes (DistNil absurdum) = DistNil absurdum
  catMaybes (DistEither f x y) = DistEither f (catMaybes x) (catMaybes y)
instance (forall f. Filterable (ap f)) => Cochoice (Dist ap p) where
  unleft (DistNil absurdum) = DistNil (absurdum . Left)
  unleft (DistEither f x y) =
    DistEither (f . Left)
      (mapMaybe (either Just (const Nothing)) x)
      (mapMaybe (either Just (const Nothing)) y)
  unright (DistNil absurdum) = DistNil (absurdum . Right)
  unright (DistEither f x y) =
    DistEither (f . Right)
      (mapMaybe (either (const Nothing) Just) x)
      (mapMaybe (either (const Nothing) Just) y)

{- | A free `Distributor` type, generated over
a `Choice` and `Cochoice`, `Applicative` `Profunctor`. -}
newtype ChooseDist p a b =
  ChooseDist {distAlts :: [ChooseApF ChooseDist p a b]}
instance (forall x. Functor (p x)) => Functor (ChooseDist p a) where
  fmap f (ChooseDist alts) = ChooseDist (map (fmap f) alts)
instance (forall x. Applicative (p x))
  => Applicative (ChooseDist p a) where
  pure b = liftChooseDist (pure b)
  ChooseDist xs <*> ChooseDist ys =
    ChooseDist [x <*> y | x <- xs, y <- ys]
instance (forall x. Applicative (p x))
  => Alternative (ChooseDist p a) where
    empty = ChooseDist []
    ChooseDist altsL <|> ChooseDist altsR = ChooseDist (altsL ++ altsR)
instance Profunctor p => Profunctor (ChooseDist p) where
  dimap f g (ChooseDist alts) = ChooseDist (map (dimap f g) alts)
instance (forall x. Applicative (p x), Profunctor p)
  => Monoidal (ChooseDist p)
instance Choice p => Choice (ChooseDist p) where
  left' (ChooseDist alts) = ChooseDist (map left' alts)
  right' (ChooseDist alts) = ChooseDist (map right' alts)
instance Cochoice p => Cochoice (ChooseDist p) where
  unleft (ChooseDist alts) = ChooseDist (map unleft alts)
  unright (ChooseDist alts) = ChooseDist (map unright alts)
instance (Choice p, Cochoice p, forall x. Applicative (p x))
  => Distributor (ChooseDist p)

liftChooseDist :: p a b -> ChooseDist p a b
liftChooseDist p = ChooseDist [ChooseAp Just (pure Just) p]

hoistChooseDist
  :: (forall x y. p x y -> q x y)
  -> ChooseDist p a b -> ChooseDist q a b
hoistChooseDist f (ChooseDist alts) =
  let
    hoistChooseAp
      :: (forall x y. p x y -> q x y)
      -> ChooseApF ChooseDist p s t
      -> ChooseApF ChooseDist q s t
    hoistChooseAp g = \case
      ChooseNil -> ChooseNil
      ChoosePure t -> ChoosePure t
      ChooseAp f' g' x -> ChooseAp f' (hoistChooseAp g g') (g x)
  in
    ChooseDist (map (hoistChooseAp f) alts)

-- TODO: ApFilter instances and functions
-- data ApFilter f a where
--   ApFilterNil :: ApFilter f a
--   ApFilterPure :: a -> ApFilter f a
--   ApFilter
--     :: f a
--     -> ApFilter f (a -> Maybe b)
--     -> ApFilter f b

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
