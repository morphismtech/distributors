{-|
Module      : Data.Distributor
Description : monoidal and distributive distributors
Copyright   : (c) Eitan Chatav, 2023
License     : LICENSE
Maintainer  : eitan.chatav@gmail.com
Stability   : experimental

The term "distributor" is a synonym for ["profunctor"]
(https://ncatlab.org/nlab/show/profunctor).
Jean Bénabou who invented the term and originally used
“profunctor,” then preferred [“distributor,”]
(http://www.entretemps.asso.fr/maths/Distributors.pdf)
which is supposed to carry the intuition that a distributor
generalizes a functor in a similar way to how a distribution
generalizes a function.
[Bénabou]
(http://cahierstgdc.com/wp-content/uploads/2022/07/F.-BORCEUX-LXIII-3.pdf)
in his time introduced the notions of enriched categories,
bicategories as well as distributors and invented the term monad.
He was lost to us on 11, February 2022
and this library is dedicated to his memory.

The class `Distributor` will mean
something more specific than "distributor",
and will be studied alongside `Monoidal` profunctors,
as well as `Choice` and `Cochoice` profunctors which relate to
`Alternative`, `Applicative` and `Filterable` functors.

Examples of `Distributor`s will include printers and parsers,
and it will be demonstrated how to write a single term for both.
The results here are a profunctorial iterpretation of
[Invertible Syntax Descriptions]
(https://www.mathematik.uni-marburg.de/~rendel/rendel10invertible.pdf)
-}
module Data.Distributor
  ( -- * lax monoidal profunctors
    Monoidal (one, (>*<)) , dimap2, (>*), (*<)
  , pureP, apP, liftA2P, replicateP, replicateP_, foreverP
    -- * lax distributive profunctors
  , Distributor (zero, (>+<), several, severalMore, possibly)
  , several1, choiceP
  , dialt, emptyP, (>|<), (>\<)
    -- * pattern matching
  , eot, onCase, inCase, dichainl, dichainl'
  ) where

import Control.Applicative hiding (WrappedArrow(..))
import Control.Arrow
import Control.Lens hiding (chosen)
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
import Data.Void
import Generics.Eot
import GHC.Base (Constraint, Type)

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
prop> one >*< p = lunit p
prop> p >*< one = runit p
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
  `one` is a symmetric analog of `pureP`.

  prop> one = pure ()
  -}
  one :: p () ()
  default one :: (forall x. Applicative (p x)) => p () ()
  one = pure ()

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
  one = id
  (>*<) = (***)
instance Monoid s => Monoidal (Forget s) where
  one = Forget mempty
  Forget f >*< Forget g = Forget (\(a,c) -> f a <> g c)
instance Divisible f => Monoidal (Clown f) where
  one = Clown conquer
  Clown x >*< Clown y = Clown (divided x y)
instance Applicative f => Monoidal (Joker f) where
  one = Joker (pure ())
  Joker x >*< Joker y = Joker ((,) <$> x <*> y)
instance Arrow p => Monoidal (Pro.WrappedArrow p) where
  one = Pro.WrapArrow returnA
  Pro.WrapArrow p >*< Pro.WrapArrow q = Pro.WrapArrow (p *** q)
instance (Monoidal p, Monoidal q)
  => Monoidal (Procompose p q) where
    one = Procompose one one
    Procompose wb aw >*< Procompose vb av =
      Procompose (wb >*< vb) (aw >*< av)
instance (Monoidal p, Monoidal q)
  => Monoidal (Product p q) where
    one = Pair one one
    Pair x0 y0 >*< Pair x1 y1 = Pair (x0 >*< x1) (y0 >*< y1)
instance Functor f => Monoidal (Costar f) where
  one = Costar (const ())
  Costar f >*< Costar g =
    Costar (\ac -> (f (fst <$> ac), g (snd <$> ac)))
instance Applicative f => Monoidal (Star f) where
  one = Star (const (pure ()))
  Star f >*< Star g =
    Star (\(a,c) -> (,) <$> f a <*> g c)
deriving via (Star m) instance Monad m => Monoidal (Kleisli m)
instance (Applicative f, Monoidal p) => Monoidal (Tannen f p) where
  one = Tannen (pure one)
  Tannen x >*< Tannen y = Tannen ((>*<) <$> x <*> y)
instance (Applicative f, Monoidal p) => Monoidal (Cayley f p) where
  one = Cayley (pure one)
  Cayley x >*< Cayley y = Cayley ((>*<) <$> x <*> y)
instance (Functor f, Applicative g, Monoidal p)
  => Monoidal (Biff p f g) where
    one = Biff (dimap (const ()) pure one)
    Biff x >*< Biff y = Biff $ dimap
      ((fst <$>) &&& (snd <$>))
      (uncurry (liftA2 (,)))
      (x >*< y)
instance Monoid s => Monoidal (PartialExchange s t)

{- | Like `pure` but with a `Monoidal` constraint,
`pureP` is a functionalization of `one`.

prop> pure = pureP
-}
pureP :: Monoidal p => b -> p a b
pureP b = dimap (const ()) (const b) one

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

{- |

>>> let a1 = tokenIs 'a' >* tokenIs '1'
>>> runPrint a1 () :: String
"a1"
>>> readP_to_S (runParse a1) "a1"
[((),"")]
>>> readP_to_S (runParse a1) "b2"
[]
-}
(>*) :: Monoidal p => p () c -> p a b -> p a b
(>*) = dimap2 (const ()) id (\_ b -> b)
infixr 1 >*

(*<) :: Monoidal p => p a b -> p () c -> p a b
(*<) = dimap2 id (const ()) (\b _ -> b)
infixr 1 *<

{- | `replicateP` is analagous to `replicateM`,
but slightly more general since it will output in
any `Stream`, not just lists.

prop> replicateP n _ | n <= 0 = _Null >?$?< one
prop> replicateP n p = _Cons >$?< p >*< replicateP (n-1) p

>>> let threeAlpha = replicateP 3 (_Guard isAlpha >?$?< token)
>>> runPrint threeAlpha "abc" :: String
"abc"
-}
replicateP
  :: (Monoidal p, Choice p, Cochoice p, Stream s t a b)
  => Int -> p a b -> p s t
replicateP n _ | n <= 0 = _Null >?$?< one
replicateP n p = _Cons >$?< p >*< replicateP (n-1) p

{- | `replicateP_` is like to `replicateM_`,
but with a `Monoidal` constraint.

prop> replicateP_ n _ | n <= 0 = pureP ()
prop> replicateP_ n p = p >* replicateP_ (n-1) p
-}
replicateP_ :: Monoidal p => Int -> p () c -> p a ()
replicateP_ n _ | n <= 0 = pureP ()
replicateP_ n p = p >* replicateP_ (n-1) p

foreverP :: Monoidal p => p () c -> p a b
foreverP p = let p' = p >* p' in p'

{- | A `Distributor`, or lax distributive profunctor,
respects distributive category structure,
that is nilary and binary products and coproducts,
`()`, `(,)`, `Void` and `Either`.

What makes distributive category structure is
the existence of structural distribution isomorphisms.

prop> Either (x,y) (x,z) <-> (x, Either y z)
prop> Either (x,z) (y,z) <-> (Either x y, z)
prop> Void <-> (x, Void)
prop> Void <-> (Void, x)

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
prop> zero >+< p = lunit p
prop> p >+< zero = runit p
prop> p >+< q >+< r = assoc ((p >+< q) >+< r)

`Distributor` is not simply equivalent to an `Alternative` `Profunctor`.
Rather, when the `Profunctor` is `Choice` and `Cochoice`, then
`Alternative` gives a default implementation for `Distributor`.
In the other direction, when a `Distributor` is `Choice` and `Cochoice`,
it can give an implementation for `Alternative` with

prop> empty = emptyP

And either,

prop> (<|>) = altL
prop> (<|>) = altR

A mathematical treatment of `Distributor`s is given by Travis Squires in
[Profunctors and Distributive Categories]
(https://central.bac-lac.gc.ca/.item?id=MR31635)
-}
type Distributor :: (Type -> Type -> Type) -> Constraint
class Monoidal p => Distributor p where

  {- |
  `zero` is a restricted `empty`.
  `zero` uses the nilary coproduct `Void` directly.

  prop> zero = empty
  -}
  zero :: p Void Void
  default zero :: (forall x. Alternative (p x)) => p Void Void
  zero = empty

  {- |
  `>+<` is analagous to `(<|>)`.
  `>+<` uses the binary coproduct `Either` directly,
  where `dialt` encodes the coproduct in a functionalized way.

  prop> p >+< q = alternate (Left p) <|> alternate (Right q)
  -}
  (>+<) :: p a b -> p c d -> p (Either a c) (Either b d)
  default (>+<)
    :: (Choice p, Cochoice p, forall x. Alternative (p x))
    => p a b -> p c d -> p (Either a c) (Either b d)
  p >+< q = alternate (Left p) <|> alternate (Right q)
  infixr 3 >+<

  several :: Stream s t a b => p a b -> p s t
  several p = apIso _Stream $ one >+< severalMore p

  severalMore :: Stream s t a b => p a b -> p (a,s) (b,t)
  severalMore p = p >*< several p

  possibly :: p a b -> p (Maybe a) (Maybe b)
  possibly p = apIso _M2E $ one >+< p

apIso :: Profunctor p => AnIso s t a b -> p a b -> p s t
apIso i p = withIso i $ \ here there -> dimap here there p

several1
  :: (Choice p, Distributor p, Stream s t a b)
  => p a b -> p s t
several1 p = _Cons >$?< severalMore p

choiceP
  :: (Foldable f, Distributor p, Choice p, Cochoice p)
  => f (p a b)
  -> p a b
choiceP = foldr (>|<) emptyP

instance Distributor (->) where
  zero = id
  (>+<) = (+++)
instance Monoid s => Distributor (Forget s) where
  zero = Forget absurd
  Forget kL >+< Forget kR = Forget (either kL kR)
instance Decidable f => Distributor (Clown f) where
  zero = Clown lost
  Clown x >+< Clown y = Clown (Con.chosen x y)
instance Alternative g => Distributor (Joker g) where
  zero = Joker empty
  Joker x >+< Joker y = Joker (Left <$> x <|> Right <$> y)
instance Applicative f => Distributor (Star f) where
  zero = Star absurd
  Star f >+< Star g =
    Star (either (fmap Left . f) (fmap Right . g))
deriving via (Star m) instance Monad m => Distributor (Kleisli m)
instance Adjunction f u => Distributor (Costar f) where
  zero = Costar unabsurdL
  Costar f >+< Costar g = Costar (bimap f g . cozipL)
instance (Applicative f, Distributor p)
  => Distributor (Tannen f p) where
    zero = Tannen (pure zero)
    Tannen x >+< Tannen y = Tannen ((>+<) <$> x <*> y)
instance (Applicative f, Distributor p)
  => Distributor (Cayley f p) where
    zero = Cayley (pure zero)
    Cayley x >+< Cayley y = Cayley ((>+<) <$> x <*> y)
instance (Adjunction f u, Applicative g, Distributor p)
  => Distributor (Biff p f g) where
    zero = Biff (dimap unabsurdL absurd zero)
    Biff x >+< Biff y = Biff $ dimap
      cozipL
      (either (Left <$>) (Right <$>))
      (x >+< y)
instance (ArrowZero p, ArrowChoice p)
  => Distributor (Pro.WrappedArrow p) where
    zero = zeroArrow
    (>+<) = (+++)
instance (Distributor p, Distributor q)
  => Distributor (Procompose p q) where
    zero = Procompose zero zero
    Procompose xL yL >+< Procompose xR yR =
      Procompose (xL >+< xR) (yL >+< yR)
instance (Distributor p, Distributor q)
  => Distributor (Product p q) where
    zero = Pair zero zero
    Pair x0 y0 >+< Pair x1 y1 = Pair (x0 >+< x1) (y0 >+< y1)
instance Monoid s => Distributor (PartialExchange s t)

dialt
  :: Distributor p
  => (s -> Either a c)
  -> (b -> t)
  -> (d -> t)
  -> p a b -> p c d -> p s t
dialt f g h p q = dimap f (either g h) (p >+< q)

emptyP
  :: (Choice p, Cochoice p, Distributor p)
  => p a b
emptyP = dimapMaybe (const Nothing) absurd zero

(>|<)
  :: (Choice p, Cochoice p, Distributor p)
  => p a b -> p a b -> p a b
p >|< q = fst (discriminate (p >+< q))
infixr 3 >|<

(>\<)
  :: (Choice p, Cochoice p, Distributor p)
  => p a b -> p a b -> p a b
p >\< q = snd (discriminate (p >+< q))

{- | We can use positional pattern matching
with `eot` to construct a `Distributor`.

>>> import qualified GHC.Generics as GHC
>>> import qualified Generics.Eot as EOT
>>> :{
data FullName
  = Nameless
  | OneName String
  | FirstLast String String
  | FirstInitialsLast (Maybe String) String String
  deriving stock (Read, Show, GHC.Generic)
:}
>>> :{
fullName :: (Syntax Char Char p, Choice p, Cochoice p, Distributor p) => p FullName FullName
fullName = eot $
  one
  >+< several (satisfies isAlpha) >*< one
  >+< several (satisfies isAlpha) *< tokenIs ' ' >*< several (satisfies isAlpha) >*< one
  >+< possibly (several (satisfies isAlpha))
      >*< several (satisfies isAlpha) *< tokenIs ' '
      >*< several (satisfies isAlpha)
      >*< one
  >+< zero
:}

:{
data FullName
  = Nameless
  | OneName String
  | FirstLast String String
  | FirstInitialsLast (Maybe String) String String
  deriving stock (Read, Show, GHC.Generic)
:}

:{
fullName :: (Syntax Char Char p, Choice p, Cochoice p, Distributor p) => p FullName FullName
fullName = eot $
  one
  >+< name >*< one
  >+< name >*< name >*< one
  >+< possibly name
    >*< name
    >*< name
    >*< one
  >+< zero
    where
      name = _Cons
        >$?< satisfies isUpper
        >*< several1 (satisfies isAlpha)
      initial = satisfies isUpper *< tokenIs '.'
:}

>>> :{
fullName
  :: ( Syntax Char Char p
     , Choice p, Cochoice p
     , Distributor p
     )
  => p FullName FullName
fullName = eot $
  one
  >+< name >*< one
  >+< name *< reqSpace >*< name >*< one
  >+< possibly (name *< reqSpace)
      >*< several1 initial *< reqSpace
      >*< name
      >*< one
    where
      name = _Cons
        >$?< satisfies isUpper
        >*< several1 (satisfies isAlpha)
      initial = satisfies isUpper *< tokenIs '.'
      optSpace = _Normal "" >?$?< several1 (satisfies isSpace)
      reqSpace = _Normal " " >?$?< several1 (satisfies isSpace)
:}
-}
eot
  :: (HasEot a, HasEot b, Profunctor p)
  => p (Eot a) (Eot b) -> p a b
eot = dimap toEot fromEot

-- inexhaustive abstract pattern matching
inCase
  :: (Choice p, Cochoice p, forall x. Alternative (p x))
  => APartialIso s t a b
  -> p a b
  -> p s t
  -> p s t
inCase i = flip (<|>) . (>?$?<) i

-- exhaustive abstract pattern matching
onCase
  :: (Cochoice p, Distributor p)
  => APrism b a t s
  -> p a b
  -> p c Void
  -> p s t
onCase p =
  flip (dialt Right absurd id) . (>?$<) p

dichainl
  :: forall p s t a b. (Choice p, Cochoice p, Distributor p)
  => APartialIso s t (s,(a,s)) (t,(b,t))
  -> p a b
  -> p s t
  -> p s t
dichainl i opr arg =
  coPartialIso (difoldl (coPartialIso i)) >?$?<
    arg >*< several @p @[(a,s)] (opr >*< arg)

dichainl'
  :: forall p s a. (Cochoice p, Distributor p)
  => APrism' (s,(a,s)) s
  -> p a a
  -> p s s
  -> p s s
dichainl' p opr arg =
  difoldl' p >?$< arg >*< several @p @[(a,s)] (opr >*< arg)
