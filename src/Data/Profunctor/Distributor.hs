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
  , someP
  , sep
  , sep1
  , sepSome
    -- * Sep
  , By (..)
  , by
    -- * Free Distributive Profunctors
  , Dist (..)
  , FreeDistributor (..)
  , foldFilterDist
  , ChooseDist (..)
  , foldChooseDist
  , FilterAp (..)
  , liftFilterAp
  , hoistFilterAp
  , foldFilterAp
    -- * pattern matching
  , eot, onCase, onCocase
  , dichainl, dichainr, dichainl', dichainr'
  ) where

import Control.Applicative hiding (WrappedArrow(..))
import Control.Applicative.Filterable
import qualified Control.Applicative.Free as Free
import qualified Control.Applicative.Free.Fast as Fast
import qualified Control.Applicative.Free.Final as Final
import Control.Arrow
import Control.Lens hiding (chosen, Traversing)
import Control.Lens.Internal.Profunctor
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
import Data.Profunctor.Choose
import Data.Profunctor.Composition
import Data.Kind
import Data.Profunctor.Monad
import Data.Profunctor.Monoidal
import Data.Profunctor.Yoneda
import Data.Quiver.Functor
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
  `manyP` is the Kleene star operator, of zero or more times.
  -}
  manyP :: Stream s t a b => p a b -> p s t
  manyP p = mapIso _Stream $ oneP >+< many1 p

  {- |
  `many1` is the Kleene plus operator, of one or more times.
  -}
  many1
    :: Stream s t a b
    => p a b -> p (a,s) (b,t)
  many1 p = p >*< manyP p

  {- |
  `optionP` is zero or one times.
  -}
  optionP :: p a b -> p (Maybe a) (Maybe b)
  optionP p = mapIso _M2E $ oneP >+< p

{- | Like `many1`, but conses the token to the stream. -}
someP
  :: (Choice p, Distributor p, Stream s t a b, Cons s t a b)
  => p a b -> p s t
someP p = _Cons >? many1 p

{- | At least zero operator with a separator. -}
sep
  :: (Distributor p, Stream s t a b)
  => By p -> p a b -> p s t
sep (By comma beg end) p = mapIso _Stream $
  beg >* (oneP >+< p >*< manyP (comma >* p)) *< end

{- | More than zero operator with a separator. -}
sep1
  :: (Distributor p, Stream s t a b)
  => By p -> p a b -> p (a,s) (b,t)
sep1 (By comma beg end) p =
  beg >* p >*< manyP (comma >* p) *< end

{- | Like `sep1`, but conses the token to the stream. -}
sepSome
  :: (Distributor p, Choice p, Stream s t a b, Cons s t a b)
  => By p -> p a b -> p s t
sepSome s p = _Cons >? sep1 s p

{- | Used to parse multiple times, delimited `by` a separator,
a `beginBy`, and an `endBy`. -}
data By p = By
  { beginBy :: p () ()
  , endBy :: p () ()
  , separator :: p () ()
  }

{- | A default `By` which can be modified by updating
`beginBy`, or `endBy` fields -}
by :: Monoidal p => p () () -> By p
by = By oneP oneP

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
deriving newtype instance Distributor p
  => Distributor (WrappedMonoidal p)
instance (Distributor p, Applicative f)
  => Distributor (WrappedPafb f p) where
    zeroP = WrapPafb (emptyP absurd)
    WrapPafb ab >+< WrapPafb cd =
      WrapPafb (dialt id (fmap Left) (fmap Right) ab cd)

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

{- | `Dist` @ap@ is a free `Distributor`
when @ap@ is a free `Applicative`.

`Dist` `FilterAp` is a free `Filterable`,
`Cochoice` `Distributor`.
-}
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

instance QFunctor (Dist Free.Ap) where
  qmap g = \case
    DistNil f -> DistNil f
    DistEither f fastAp x ->
      DistEither f (Free.runAp (Free.liftAp . g) fastAp) (qmap g x)
instance QFunctor (Dist Final.Ap) where
  qmap g = \case
    DistNil f -> DistNil f
    DistEither f fastAp x ->
      DistEither f (Final.runAp (Final.liftAp . g) fastAp) (qmap g x)
instance QFunctor (Dist Fast.Ap) where
  qmap g = \case
    DistNil f -> DistNil f
    DistEither f fastAp x ->
      DistEither f (Fast.runAp (Fast.liftAp . g) fastAp) (qmap g x)
instance QFunctor (Dist FilterAp) where
  qmap g = \case
    DistNil f -> DistNil f
    DistEither f filterAp x ->
      DistEither f
        (foldFilterAp (liftFilterAp . g) filterAp)
        (qmap g x)
instance QPointed (Dist Free.Ap) where
  qsingle x = DistEither Left (Free.liftAp x) (DistNil id)
instance QPointed (Dist Final.Ap) where
  qsingle x = DistEither Left (Final.liftAp x) (DistNil id)
instance QPointed (Dist Fast.Ap) where
  qsingle x = DistEither Left (Fast.liftAp x) (DistNil id)
instance QPointed (Dist FilterAp) where
  qsingle x = DistEither Left (liftFilterAp x) (DistNil id)
class (QMonad dist, forall p. Distributor (dist p))
  => FreeDistributor dist where
    foldDist
      :: Distributor q
      => (forall x y. p x y -> q x y)
      -> dist p a b -> q a b
instance FreeDistributor (Dist Free.Ap) where
  foldDist k
    = unWrapMonoidal
    . foldDistAp Free.runAp (WrapMonoidal . k)
instance FreeDistributor (Dist Final.Ap) where
  foldDist k
    = unWrapMonoidal
    . foldDistAp Final.runAp (WrapMonoidal . k)
instance FreeDistributor (Dist Fast.Ap) where
  foldDist k
    = unWrapMonoidal
    . foldDistAp Fast.runAp (WrapMonoidal . k)
instance QMonad (Dist Free.Ap) where
  qjoin = foldDist id
instance QMonad (Dist Final.Ap) where
  qjoin = foldDist id
instance QMonad (Dist Fast.Ap) where
  qjoin = foldDist id
instance QMonad (Dist FilterAp) where
  qjoin = foldFilterDist id

foldFilterDist
  :: forall p q a b.
     ( Distributor q
     , forall s. Filterable (q s)
     )
  => (forall x y. p x y -> q x y)
  -> Dist FilterAp p a b -> q a b
foldFilterDist k
  = unWrapMonoidal
  . foldDistAp foldFilterAp (WrapMonoidal . k)

liftDistAp :: ap (p a) b -> Dist ap p a b
liftDistAp x = DistEither Left x (DistNil id)

foldDistAp
  :: Distributor q
  => (forall s t. (forall x y. p x y -> q x y) -> ap (p s) t -> q s t)
     -- ^ use the @runAp@ fold-function of the free `Applicative` @ap@
  -> (forall x y. p x y -> q x y)
  -> Dist ap p a b -> q a b
foldDistAp foldAp k = \case
  DistNil f -> emptyP f
  DistEither f b x ->
    altP f (foldAp k b) (foldDistAp foldAp k x)

instance (forall f. Functor (ap f))
  => Functor (Dist ap p a) where fmap = rmap
instance (forall f. Applicative (ap f))
  => Applicative (Dist ap p a) where
  pure b = liftDistAp (pure b)
  -- 0*x=0
  liftA2 _ (DistNil vac) _ = DistNil vac
  -- (x+y)*z=x*z+y*z
  liftA2 g (DistEither f x y) z =
    let
      ff a = bimap (,a) (,a) (f a)
    in
      altP ff
        (uncurry g <$> (liftDistAp x >*< z))
        (uncurry g <$> (y >*< z))
instance (forall f. Functor (ap f))
  => Profunctor (Dist ap p) where
  dimap f _ (DistNil vac) = DistNil (vac . f)
  dimap f' g' (DistEither f x y) =
    DistEither (f . f') (g' <$> x) (g' <$> y)
instance (forall f. Applicative (ap f)) => Monoidal (Dist ap p)
instance (forall f. Applicative (ap f))
  => Distributor (Dist ap p) where
  zeroP = DistNil absurd
  -- 0+x=x
  DistNil vac >+< x =
    dimap (either (absurd . vac) id) Right x
  -- (x+y)+z=x+(y+z)
  DistEither f x y >+< z =
    let
      assocE (Left (Left a)) = Left a
      assocE (Left (Right b)) = Right (Left b)
      assocE (Right c) = Right (Right c)
      f' = assocE . either (Left . f) Right
    in
      dialt f' Left id (liftDistAp x) (y >+< z)
instance (forall f. Filterable (ap f)) => Filterable (Dist ap p x) where
  catMaybes (DistNil vac) = DistNil vac
  catMaybes (DistEither f x y) = DistEither f (catMaybes x) (catMaybes y)
instance (forall f. Filterable (ap f)) => Cochoice (Dist ap p) where
  unleft (DistNil vac) = DistNil (vac . Left)
  unleft (DistEither f x y) =
    DistEither (f . Left)
      (mapMaybe (either Just (const Nothing)) x)
      (mapMaybe (either Just (const Nothing)) y)
  unright (DistNil vac) = DistNil (vac . Right)
  unright (DistEither f x y) =
    DistEither (f . Right)
      (mapMaybe (either (const Nothing) Just) x)
      (mapMaybe (either (const Nothing) Just) y)

{- | `ChooseDist` is the free `Choice` and `Cochoice`,
`Alternative` `Distributor`.
-}
newtype ChooseDist p a b =
  ChooseDist {distAlts :: [ChooseMonF ChooseDist p a b]}
instance Functor (ChooseDist p a) where
  fmap f (ChooseDist alts) = ChooseDist (map (fmap f) alts)
instance Applicative (ChooseDist p a) where
  pure b = ChooseDist [ChoosePure b]
  ChooseDist xs <*> y =
    let
      chooseDistAp
        :: ChooseDist p a b
        -> ChooseMonF ChooseDist p a (b -> t)
        -> ChooseDist p a t
      chooseDistAp = undefined
    in
      ChooseDist (distAlts . chooseDistAp y =<< xs)
instance Alternative (ChooseDist p a) where
    empty = ChooseDist []
    ChooseDist altsL <|> ChooseDist altsR = ChooseDist (altsL ++ altsR)
instance Profunctor (ChooseDist p) where
  dimap f g (ChooseDist alts) = ChooseDist (map (dimap f g) alts)
instance Monoidal (ChooseDist p)
instance Choice (ChooseDist p) where
  left' (ChooseDist alts) = ChooseDist (map left' alts)
  right' (ChooseDist alts) = ChooseDist (map right' alts)
instance Cochoice (ChooseDist p) where
  unleft (ChooseDist alts) = ChooseDist (map unleft alts)
  unright (ChooseDist alts) = ChooseDist (map unright alts)
instance Distributor (ChooseDist p)
instance QFunctor ChooseDist where
  qmap f (ChooseDist alts) =
    let
      hoistChooseMonF
        :: (forall x y. p x y -> q x y)
        -> ChooseMonF ChooseDist p s t
        -> ChooseMonF ChooseDist q s t
      hoistChooseMonF g = \case
        ChooseNil -> ChooseNil
        ChoosePure t -> ChoosePure t
        ChooseAp f' g' x ->
          ChooseAp f' (qmap g g') (g x)
    in
      ChooseDist (map (hoistChooseMonF f) alts)
instance QPointed ChooseDist where
  qsingle p = ChooseDist [ChooseAp Just (pure Just) p]
instance QMonad ChooseDist where
  qjoin = foldChooseDist id

-- data KleeneDist p a b where
--   DistAlts
--     :: [ChooseMonF KleeneDist p a b]
--     -> KleeneDist p a b
--   DistSev
--     :: Stream s t a b
--     => ChooseMonF KleeneDist p a b
--     -> KleeneDist p s t
-- instance Profunctor (KleeneDist p) where
--   dimap f g (DistAlts alts) = DistAlts (map (dimap f g) alts)
--   dimap f g (DistSev p) = DistSev (dimapMaybe (_ f) (_ g) p)

foldChooseDist
  :: forall p q a b.
     ( Choice q
     , Cochoice q
     , forall s. Alternative (q s)
     )
  => (forall x y. p x y -> q x y)
  -> ChooseDist p a b -> q a b
foldChooseDist u chooseDist = go chooseDist where

  go :: forall s t. ChooseDist p s t -> q s t
  go (ChooseDist alts) =
    foldr (\r alt -> go2 r <|> alt) empty alts

  go2 :: forall s t. ChooseMonF ChooseDist p s t -> q s t
  go2 = \case
    ChooseNil -> empty
    ChoosePure b -> pure b
    ChooseAp f alt x -> catMaybesP (go alt <*> dimapMaybe f Just (u x))

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
    sev = manyP @p @[a]
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
    sev = manyP @p @[a]
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
    sev = manyP @p @[a]
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
    sev = manyP @p @[a]
  in
    difoldr' p ?< sev (opr >* arg) >*< arg 
