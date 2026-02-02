{-|
Module      : Data.Profunctor.Distributor
Description : distributors
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Data.Profunctor.Distributor
  ( -- * Distributor
    Distributor (..), dialt
    -- * Alternator
  , Alternator (..)
  , choiceP
  , optionP
    -- * Homogeneous
  , Homogeneous (..)
    -- * SepBy
  , SepBy (..)
  , sepBy
  , noSep
  , several
  , several1
  , chain
  , chain1
  ) where

import Control.Applicative hiding (WrappedArrow)
import Control.Applicative qualified as Ap (WrappedArrow)
import Control.Arrow
import Control.Lens hiding (chosen)
import Control.Lens.Internal.Profunctor
import Control.Lens.PartialIso
import Data.Bifunctor.Clown
import Data.Bifunctor.Joker
import Data.Bifunctor.Product
import Data.Complex
import Data.Foldable hiding (toList)
import Data.Functor.Adjunction
import Data.Functor.Compose
import Data.Functor.Contravariant.Divisible
import qualified Data.Functor.Product as Functor
import qualified Data.Functor.Sum as Functor
import qualified Data.Monoid as Monoid
import Data.Profunctor hiding (WrappedArrow)
import Data.Profunctor qualified as Pro (WrappedArrow)
import Data.Profunctor.Cayley
import Data.Profunctor.Composition
import Data.Profunctor.Monad
import Data.Profunctor.Monoidal
import Data.Profunctor.Yoneda
import Data.Proxy
import Data.Sequence (Seq)
import Data.Tagged
import Data.Tree (Tree (..))
import Data.Vector (Vector)
import Data.Void
import GHC.Exts
import GHC.Generics

-- Distributor --

{- | A `Distributor`, or lax distributive profunctor,
respects [distributive category]
(https://ncatlab.org/nlab/show/distributive+category)
structure, that is nilary and binary products and coproducts,
@()@, @(,)@, `Void` and `Either`. It has zero `zeroP`
and sum `>+<` lax monoidal structure morphisms.

In addition to the product laws for `Monoidal`, we have
sum laws for `Distributor`.

Laws:

>>> let lunit = dimap (either absurd id) Right
>>> let runit = dimap (either id absurd) Left
>>> :{
let assoc = dimap
      (either (Left . Left) (either (Left . Right) Right))
      (either (either Left (Right . Left)) (Right . Right))
:}

prop> zeroP >+< p = lunit p
prop> p >+< zeroP = runit p
prop> p >+< q >+< r = assoc ((p >+< q) >+< r)
prop> dimap (f >+< g) (h >+< i) (p >+< q) = dimap f h p >+< dimap g i q

-}
class Monoidal p => Distributor p where

  {- | The zero structure morphism of a `Distributor`.

  `zeroP` has a default for `Alternator`.

  prop> zeroP = empty
  -}
  zeroP :: p Void Void
  default zeroP :: Alternator p => p Void Void
  zeroP = empty

  {- | The sum structure morphism of a `Distributor`.
  
  `>+<` has a default for `Alternator`.

  prop> x >+< y = alternate (Left x) <|> alternate (Right y)
  -}
  (>+<) :: p a b -> p c d -> p (Either a c) (Either b d)
  default (>+<)
    :: Alternator p
    => p a b -> p c d -> p (Either a c) (Either b d)
  x >+< y = alternate (Left x) <|> alternate (Right y)
  infixr 3 >+<

  {- | One or none. -}
  optionalP :: p a b -> p (Maybe a) (Maybe b)
  optionalP p = eotMaybe >~ oneP >+< p

  {- | Zero or more. -}
  manyP :: p a b -> p [a] [b]
  manyP p = eotList >~ oneP >+< p >*< manyP p

instance Distributor (->) where
  zeroP = id
  (>+<) = (+++)
instance Monoid s => Distributor (Forget s) where
  zeroP = Forget absurd
  Forget kL >+< Forget kR = Forget (either kL kR)
instance Decidable f => Distributor (Clown f) where
  zeroP = Clown lost
  Clown x >+< Clown y = Clown (chosen x y)
instance Alternative f => Distributor (Joker f) where
  zeroP = Joker empty
  Joker x >+< Joker y = Joker (Left <$> x <|> Right <$> y)
  optionalP (Joker x) = Joker (optional x)
  manyP (Joker x) = Joker (many x)
instance (Distributor p, Applicative f)
  => Distributor (WrappedPafb f p) where
    zeroP = WrapPafb (rmap pure zeroP)
    WrapPafb x >+< WrapPafb y = WrapPafb $
      dialt id (fmap Left) (fmap Right) x y
    manyP (WrapPafb x) = WrapPafb (rmap sequenceA (manyP x))
    optionalP (WrapPafb x) = WrapPafb (rmap sequenceA (optionalP x))
instance Applicative f => Distributor (Star f) where
  zeroP = Star absurd
  Star f >+< Star g =
    Star (either (fmap Left . f) (fmap Right . g))
  optionalP (Star f) = Star (traverse f)
  manyP (Star f) = Star (traverse f)
deriving via (Star m) instance Monad m => Distributor (Kleisli m)
instance Adjunction f u => Distributor (Costar f) where
  zeroP = Costar unabsurdL
  Costar f >+< Costar g = Costar (bimap f g . cozipL)
instance (Applicative f, Distributor p)
  => Distributor (Cayley f p) where
    zeroP = Cayley (pure zeroP)
    Cayley x >+< Cayley y = Cayley ((>+<) <$> x <*> y)
    optionalP (Cayley x) = Cayley (optionalP <$> x)
    manyP (Cayley x) = Cayley (manyP <$> x)
instance (ArrowZero p, ArrowChoice p)
  => Distributor (Pro.WrappedArrow p) where
    zeroP = zeroArrow
    (>+<) = (+++)
deriving via (Pro.WrappedArrow p)
  instance (ArrowZero p, ArrowChoice p)
    => Distributor (Ap.WrappedArrow p)
instance (Distributor p, Distributor q)
  => Distributor (Procompose p q) where
    zeroP = Procompose zeroP zeroP
    Procompose xL yL >+< Procompose xR yR =
      Procompose (xL >+< xR) (yL >+< yR)
    optionalP (Procompose f g) =
      Procompose (optionalP f) (optionalP g)
    manyP (Procompose f g) =
      Procompose (manyP f) (manyP g)
instance (Distributor p, Distributor q)
  => Distributor (Product p q) where
    zeroP = Pair zeroP zeroP
    Pair x0 y0 >+< Pair x1 y1 = Pair (x0 >+< x1) (y0 >+< y1)
    optionalP (Pair f g) =
      Pair (optionalP f) (optionalP g)
    manyP (Pair f g) =
      Pair (manyP f) (manyP g)
instance Distributor p => Distributor (Yoneda p) where
  zeroP = proreturn zeroP
  ab >+< cd = proreturn (proextract ab >+< proextract cd)
  optionalP = proreturn . optionalP . proextract
  manyP = proreturn . manyP . proextract
instance Distributor p => Distributor (Coyoneda p) where
  zeroP = proreturn zeroP
  ab >+< cd = proreturn (proextract ab >+< proextract cd)
  optionalP = proreturn . optionalP . proextract
  manyP = proreturn . manyP . proextract

{- | `dialt` is a functionalized form of `>+<`. -}
dialt
  :: Distributor p
  => (s -> Either a c)
  -> (b -> t)
  -> (d -> t)
  -> p a b -> p c d -> p s t
dialt f g h p q = dimap f (either g h) (p >+< q)

{- | A class of `Homogeneous`
countable sums of countable products.
-}
class Traversable t => Homogeneous t where
  {- | Sequences actions `homogeneously`.

  prop> homogeneously @Maybe = optionalP
  prop> homogeneously @[] = manyP
  
  Any `Traversable` & `Distributive` countable product
  can be given a default implementation for the `homogeneously` method.

  prop> homogeneously = ditraverse

  And any user-defined homogeneous algebraic datatype has
  a default instance for `Homogeneous`, by deriving `Generic1`.
  -}
  homogeneously :: Distributor p => p a b -> p (t a) (t b)
  default homogeneously
    :: (Generic1 t, Homogeneous (Rep1 t), Distributor p)
    => p a b -> p (t a) (t b)
  homogeneously = dimap from1 to1 . homogeneously
instance Homogeneous Par1 where
  homogeneously = dimap unPar1 Par1
instance Homogeneous Identity where
  homogeneously = dimap runIdentity Identity
instance Homogeneous Monoid.Dual where
  homogeneously = dimap Monoid.getDual Monoid.Dual
instance Homogeneous Monoid.Product where
  homogeneously = dimap Monoid.getProduct Monoid.Product
instance Homogeneous Monoid.Sum where
  homogeneously = dimap Monoid.getSum Monoid.Sum
instance Homogeneous (Tagged s) where
  homogeneously = dimap unTagged Tagged
instance Homogeneous U1 where
  homogeneously _ = pure U1
instance Homogeneous (K1 i ()) where
  homogeneously _ = pure (K1 ())
instance Homogeneous (Const ()) where
  homogeneously _ = pure (Const ())
instance Homogeneous Proxy where
  homogeneously _ = pure Proxy
instance (Homogeneous s, Homogeneous t)
  => Homogeneous (s :.: t) where
    homogeneously
      = dimap unComp1 Comp1
      . homogeneously . homogeneously
instance (Homogeneous s, Homogeneous t)
  => Homogeneous (Compose s t) where
    homogeneously
      = dimap getCompose Compose
      . homogeneously . homogeneously
instance (Homogeneous s, Homogeneous t)
  => Homogeneous (s :*: t) where
    homogeneously p = dimap2
      (\(s :*: _) -> s)
      (\(_ :*: t) -> t)
      (:*:)
      (homogeneously p)
      (homogeneously p)
instance (Homogeneous s, Homogeneous t)
  => Homogeneous (Functor.Product s t) where
    homogeneously p = dimap2
      (\(Functor.Pair s _) -> s)
      (\(Functor.Pair _ t) -> t)
      Functor.Pair
      (homogeneously p)
      (homogeneously p)
instance Homogeneous V1 where
  homogeneously _ = dimap (\case) (\case) zeroP
instance Homogeneous (K1 i Void) where
  homogeneously _ = dimap unK1 K1 zeroP
instance Homogeneous (Const Void) where
  homogeneously _ = dimap getConst Const zeroP
instance (Homogeneous s, Homogeneous t)
  => Homogeneous (s :+: t) where
    homogeneously p = dialt
      (\case {L1 s -> Left s; R1 t -> Right t})
      L1
      R1
      (homogeneously p)
      (homogeneously p)
instance (Homogeneous s, Homogeneous t)
  => Homogeneous (Functor.Sum s t) where
    homogeneously p = dialt
      (\case {Functor.InL s -> Left s; Functor.InR t -> Right t})
      Functor.InL
      Functor.InR
      (homogeneously p)
      (homogeneously p)
instance Homogeneous t
  => Homogeneous (M1 i c t) where
    homogeneously = dimap unM1 M1 . homogeneously
instance Homogeneous f => Homogeneous (Rec1 f) where
  homogeneously = dimap unRec1 Rec1 . homogeneously
instance Homogeneous Maybe where
  homogeneously = optionalP
instance Homogeneous [] where
  homogeneously = manyP
instance Homogeneous Vector where
  homogeneously p = eotList >~ oneP >+< p >*< homogeneously p
instance Homogeneous Seq where
  homogeneously p = eotList >~ oneP >+< p >*< homogeneously p
instance Homogeneous Complex where
  homogeneously p = dimap2 realPart imagPart (:+) p p
instance Homogeneous Tree where
  homogeneously p = dimap2 rootLabel subForest Node p (manyP (homogeneously p))

-- Alternator --

{- | The `Alternator` class co-extends `Choice` and `Distributor`,
as well as `Alternative`, adding the `alternate` method,
which is a lax monoidal structure morphism on sums.

For the case of `Functor`s the analog of `alternate` can be defined
without any other constraint, but the case of `Profunctor`s turns
out to be slighly more complex.
-}
class (Choice p, Distributor p, forall x. Alternative (p x))
  => Alternator p where

    {- |
    prop> left' = alternate . Left
    prop> right' = alternate . Right
    prop> zeroP = empty
    prop> x >+< y = alternate (Left x) <|> alternate (Right y)

    `alternate` has a default for `Cochoice`.
    -}
    alternate
      :: Either (p a b) (p c d)
      -> p (Either a c) (Either b d)
    default alternate
      :: Cochoice p
      => Either (p a b) (p c d)
      -> p (Either a c) (Either b d)
    alternate =
      dimapMaybe (either Just (pure Nothing)) (Just . Left)
      |||
      dimapMaybe (either (pure Nothing) Just) (Just . Right)

    {- | One or more. -}
    someP :: p a b -> p [a] [b]
    someP p = _Cons >? p >*< manyP p

choiceP :: (Foldable f, Alternator p) => f (p a b) -> p a b
choiceP = foldl' (<|>) empty

optionP :: Alternator p => b -> p a b -> p a b
optionP b p = p <|> pure b

instance (Alternator p, Applicative f)
  => Alternator (WrappedPafb f p) where
    alternate =
      let
        f = WrapPafb
          . rmap (either (fmap Left) pure)
          . alternate
          . Left
          . unwrapPafb
        g = WrapPafb
          . rmap (either pure (fmap Right))
          . alternate
          . Right
          . unwrapPafb
      in
        either f g

    someP (WrapPafb x) = WrapPafb (rmap sequenceA (someP x))
instance Alternator p => Alternator (Coyoneda p) where
  alternate (Left p) = proreturn (alternate (Left (proextract p)))
  alternate (Right p) = proreturn (alternate (Right (proextract p)))
  someP = proreturn . someP . proextract
instance Alternator p => Alternator (Yoneda p) where
  alternate (Left p) = proreturn (alternate (Left (proextract p)))
  alternate (Right p) = proreturn (alternate (Right (proextract p)))
  someP = proreturn . someP . proextract

{- | Used to sequence multiple times,
separated by a `separateBy`,
begun by a `beginBy`,
and ended by an `endBy`. -}
data SepBy p = SepBy
  { beginBy :: p
  , endBy :: p
  , separateBy :: p
  } deriving stock
    ( Functor, Foldable, Traversable
    , Eq, Ord, Show, Read
    )

{- | A `SepBy` smart constructor,
setting the `separateBy` field,
with no beginning or ending delimitors,
except by updating `beginBy` or `endBy` fields. -}
sepBy :: Monoidal p => p () () -> SepBy (p () ())
sepBy = SepBy oneP oneP

{- | A `SepBy` smart constructor for no separator,
beginning or ending delimiters. -}
noSep :: Monoidal p => SepBy (p () ())
noSep = sepBy oneP

{- |
prop> several noSep = manyP
-}
several
  :: (IsList s, IsList t, Distributor p)
  => SepBy (p () ()) -> p (Item s) (Item t) -> p s t
several (SepBy beg end sep) p = iso toList fromList . eotList >~
  beg >* (oneP >+< p >*< manyP (sep >* p)) *< end

{- |
prop> several1 noSep p = someP p
-}
several1
  :: (IsList s, IsList t, Distributor p, Choice p)
  => SepBy (p () ()) -> p (Item s) (Item t) -> p s t
several1 (SepBy beg end sep) p = iso toList fromList . _Cons >?
  beg >* (p >*< manyP (sep >* p)) *< end

chain
  :: Alternator p
  => (forall x. x -> Either x x) -- ^ `Left` or `Right` associate
  -> APartialIso a b (a,a) (b,b) -- ^ binary constructor pattern
  -> APrism a b () () -- ^ nilary constructor pattern
  -> SepBy (p () ()) -> p a b -> p a b
chain association pat2 pat0 (SepBy beg end sep) p =
  beg >* (pat0 >? oneP <|> chain1 association pat2 (sepBy sep) p) *< end

chain1
  :: (Distributor p, Choice p)
  => (forall x. x -> Either x x) -- ^ `Left` or `Right` associate
  -> APartialIso a b (a,a) (b,b) -- ^ binary constructor pattern
  -> SepBy (p () ()) -> p a b -> p a b
chain1 association pat (SepBy beg end sep) = leftOrRight chainl1 chainr1
  where
    leftOrRight a b = case association () of Left _ -> a; Right _ -> b
    chainl1 p = difoldl pat >? beg >* p >*< manyP (sep >* p) *< end
    chainr1 p = difoldr pat >? beg >* manyP (p *< sep) >*< p *< end
