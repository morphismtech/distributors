{- |
Module      : Data.Monoid.Disjunctive
Description : disjunctive monoids, Boolean & Kleene star algebras
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable

See Boole, [The Mathematical Analysis of Logic]
(https://www.gutenberg.org/files/36884/36884-pdf.pdf),
and Kleene, [Representation of Events in Nerve Nets and Finite Automata]
(https://www.rand.org/pubs/research_memoranda/RM704.html).
-}

module Data.Monoid.Disjunctive
  ( -- * DisjunctiveMonoid
    DisjunctiveMonoid (..)
  , orP, anyP
    -- * BooleanAlgebra
  , BooleanAlgebra (..)
  , andP, allP
    -- * KleeneStarAlgebra
  , KleeneStarAlgebra (..)
  ) where

import Control.Applicative
import Control.Arrow
import Control.Lens.Internal.Profunctor
import Control.Monad
import Data.Bifunctor.Joker
import Data.Bifunctor.Product qualified as Bifunctor
import Data.Functor.Compose
import Data.Functor.Contravariant
import Data.Functor.Identity
import Data.Functor.Product qualified as Functor
import Data.Monoid
import Data.Profunctor hiding (WrappedArrow (..))
import Data.Profunctor qualified as Pro (WrappedArrow (..))
import Data.Profunctor.Cayley
import Data.Profunctor.Monad
import Data.Profunctor.Yoneda
import Data.Proxy
import GHC.Conc (STM)
import GHC.Generics
import Text.ParserCombinators.ReadP (ReadP)
import Text.ParserCombinators.ReadPrec (ReadPrec)

{- | A `DisjunctiveMonoid` is simply a monoid,
the only difference from `Monoid` being its semantics
are disjunctive logical "or" constructs.

It has a disjunction `>|<` with identity `falseP`,
like `Alternative`'s `<|>` & `empty`.

prop> falseP >|< x = x = x >|< falseP
prop> (x >|< y) >|< z = x >|< (y >|< z)
-}
class DisjunctiveMonoid a where

  -- | identity of disjunction
  falseP :: a
  default falseP :: (a ~ f x, Alternative f) => a
  falseP = empty

  -- | disjunction
  (>|<) :: a -> a -> a
  default (>|<) :: (a ~ f x, Alternative f) => a -> a -> a
  (>|<) = (<|>)
  infixl 3 >|<

-- | cumulative disjunction
orP :: (Foldable f, DisjunctiveMonoid a) => f a -> a
orP = foldl' (>|<) falseP

-- | existential
anyP :: (Foldable f, DisjunctiveMonoid b) => (a -> b) -> f a -> b
anyP f = foldl' (\b a -> b >|< f a) falseP

{- | A `BooleanAlgebra`, like `Bool`, supporting classical logical operations,
with disjunction `>|<` & false `falseP`.
-}
class DisjunctiveMonoid b => BooleanAlgebra b where

  -- | conjunction
  (>&<) :: b -> b -> b
  default (>&<)
    :: (b ~ f bool, BooleanAlgebra bool, Applicative f) => b -> b -> b
  (>&<) = liftA2 (>&<)

  -- | negation
  notP :: b -> b
  default notP
    :: (b ~ f bool, BooleanAlgebra bool, Functor f) => b -> b
  notP = fmap notP

  -- | true
  trueP :: b
  default trueP
    :: (b ~ f bool, BooleanAlgebra bool, Applicative f) => b
  trueP = pure trueP

-- | cumulative conjunction
andP :: (Foldable f, BooleanAlgebra b) => f b -> b
andP = foldl' (>&<) trueP

-- | universal
allP :: (Foldable f, BooleanAlgebra b) => (a -> b) -> f a -> b
allP f = foldl' (\b a -> b >&< f a) trueP

{- | A `KleeneStarAlgebra` is a semiring
with a generally non-commutative multiplication,
the `Monoid` concatenation operator `<>` with identity `mempty`;
and an idempotent `DisjunctiveMonoid` addition, the alternation operator `>|<`
with identity `falseP`.

prop> x >|< x = x
prop> falseP >|< x = x = x >|< falseP
prop> falseP <> x = falseP = x <> falseP
prop> mempty <> x = x = x <> mempty

It also has three unary Kleene quantifier operators;

* `optK`, zero or one,

prop> optK x = mempty >|< x = x >|< mempty

* `plusK`, one or more,

prop> plusK x = x <> starK x = starK x <> x

* and the eponymous `starK`, zero or more.

prop> starK x = optK (plusK x)

-}
class (Monoid k, DisjunctiveMonoid k) => KleeneStarAlgebra k where
  starK, plusK, optK :: k -> k
  starK x = optK (plusK x)
  plusK x = x <> starK x
  optK x = mempty >|< x

--instances
instance DisjunctiveMonoid Bool where
  falseP = False
  (>|<) = (||)
instance BooleanAlgebra Bool where
  trueP = True
  notP = not
  (>&<) = (&&)
instance DisjunctiveMonoid Any where
  falseP = Any False
  Any x >|< Any y = Any (x || y)
instance BooleanAlgebra Any where
  trueP = Any True
  notP (Any x) = Any (not x)
  Any x >&< Any y = Any (x && y)
deriving via Generically () instance DisjunctiveMonoid ()
deriving via Generically () instance BooleanAlgebra ()
deriving via Generically () instance KleeneStarAlgebra ()
deriving via Generically (a, b)
  instance (DisjunctiveMonoid a, DisjunctiveMonoid b) => DisjunctiveMonoid (a, b)
deriving via Generically (a, b)
  instance (BooleanAlgebra a, BooleanAlgebra b) => BooleanAlgebra (a, b)
deriving via Generically (a, b)
  instance (KleeneStarAlgebra a, KleeneStarAlgebra b)
    => KleeneStarAlgebra (a, b)
deriving via Generically (a, b, c)
  instance (DisjunctiveMonoid a, DisjunctiveMonoid b, DisjunctiveMonoid c)
    => DisjunctiveMonoid (a, b, c)
deriving via Generically (a, b, c)
  instance (BooleanAlgebra a, BooleanAlgebra b, BooleanAlgebra c)
    => BooleanAlgebra (a, b, c)
deriving via Generically (a, b, c)
  instance (KleeneStarAlgebra a, KleeneStarAlgebra b, KleeneStarAlgebra c)
    => KleeneStarAlgebra (a, b, c)
deriving via Generically (a, b, c, d)
  instance (DisjunctiveMonoid a, DisjunctiveMonoid b, DisjunctiveMonoid c, DisjunctiveMonoid d)
    => DisjunctiveMonoid (a, b, c, d)
deriving via Generically (a, b, c, d)
  instance
    ( BooleanAlgebra a, BooleanAlgebra b, BooleanAlgebra c
    , BooleanAlgebra d )
    => BooleanAlgebra (a, b, c, d)
deriving via Generically (a, b, c, d)
  instance
    ( KleeneStarAlgebra a, KleeneStarAlgebra b, KleeneStarAlgebra c
    , KleeneStarAlgebra d )
    => KleeneStarAlgebra (a, b, c, d)
deriving via Generically (a, b, c, d, e)
  instance
    ( DisjunctiveMonoid a, DisjunctiveMonoid b, DisjunctiveMonoid c, DisjunctiveMonoid d
    , DisjunctiveMonoid e )
    => DisjunctiveMonoid (a, b, c, d, e)
deriving via Generically (a, b, c, d, e)
  instance
    ( BooleanAlgebra a, BooleanAlgebra b, BooleanAlgebra c
    , BooleanAlgebra d, BooleanAlgebra e )
    => BooleanAlgebra (a, b, c, d, e)
deriving via Generically (a, b, c, d, e)
  instance
    ( KleeneStarAlgebra a, KleeneStarAlgebra b, KleeneStarAlgebra c
    , KleeneStarAlgebra d, KleeneStarAlgebra e )
    => KleeneStarAlgebra (a, b, c, d, e)
instance DisjunctiveMonoid b => DisjunctiveMonoid (x -> b) where
  falseP = const falseP
  f >|< g = \x -> f x >|< g x
instance BooleanAlgebra b => BooleanAlgebra (x -> b)
instance KleeneStarAlgebra k => KleeneStarAlgebra (x -> k) where
  starK = (starK .)
  plusK = (plusK .)
  optK = (optK .)
instance DisjunctiveMonoid (Predicate a) where
  falseP = Predicate falseP
  Predicate p >|< Predicate q = Predicate (p >|< q)
instance BooleanAlgebra (Predicate a) where
  trueP = Predicate trueP
  notP (Predicate p) = Predicate (notP p)
  Predicate p >&< Predicate q = Predicate (p >&< q)
deriving via Generically (Identity a)
  instance DisjunctiveMonoid a => DisjunctiveMonoid (Identity a)
deriving via Generically (Identity a)
  instance BooleanAlgebra a => BooleanAlgebra (Identity a)
deriving via Generically (Identity a)
  instance KleeneStarAlgebra a => KleeneStarAlgebra (Identity a)
deriving via Generically (Const a b)
  instance DisjunctiveMonoid a => DisjunctiveMonoid (Const a b)
deriving via Generically (Const a b)
  instance BooleanAlgebra a => BooleanAlgebra (Const a b)
deriving via Generically (Const a b)
  instance KleeneStarAlgebra a => KleeneStarAlgebra (Const a b)
deriving via Generically (Proxy a) instance DisjunctiveMonoid (Proxy a)
deriving via Generically (Proxy a) instance BooleanAlgebra (Proxy a)
deriving via Generically (Proxy a) instance KleeneStarAlgebra (Proxy a)
instance DisjunctiveMonoid (Maybe a)
instance DisjunctiveMonoid (IO a)
instance DisjunctiveMonoid (STM a)
instance DisjunctiveMonoid (ZipList a)
instance DisjunctiveMonoid (ReadP a)
instance DisjunctiveMonoid (ReadPrec a)
instance DisjunctiveMonoid (U1 p)
instance MonadPlus m => DisjunctiveMonoid (WrappedMonad m a)
instance ArrowPlus a => DisjunctiveMonoid (WrappedArrow a b c)
instance ArrowPlus a => DisjunctiveMonoid (ArrowMonad a b)
instance DisjunctiveMonoid (f a) => DisjunctiveMonoid (Alt f a) where
  falseP = Alt falseP
  Alt x >|< Alt y = Alt (x >|< y)
instance DisjunctiveMonoid (f a) => DisjunctiveMonoid (Ap f a) where
  falseP = Ap falseP
  Ap x >|< Ap y = Ap (x >|< y)
instance (Applicative f, DisjunctiveMonoid (f k), Monoid k)
  => KleeneStarAlgebra (Ap f k)
instance DisjunctiveMonoid (f (g a)) => DisjunctiveMonoid (Compose f g a) where
  falseP = Compose falseP
  Compose x >|< Compose y = Compose (x >|< y)
instance (DisjunctiveMonoid (f a), DisjunctiveMonoid (g a))
  => DisjunctiveMonoid (Functor.Product f g a) where
    falseP = Functor.Pair falseP falseP
    Functor.Pair x0 y0 >|< Functor.Pair x1 y1 =
      Functor.Pair (x0 >|< x1) (y0 >|< y1)
instance (DisjunctiveMonoid (f p), DisjunctiveMonoid (g p))
  => DisjunctiveMonoid ((f :*: g) p) where
    falseP = falseP :*: falseP
    (x0 :*: y0) >|< (x1 :*: y1) = (x0 >|< x1) :*: (y0 >|< y1)
instance DisjunctiveMonoid (f (g p)) => DisjunctiveMonoid ((f :.: g) p) where
  falseP = Comp1 falseP
  Comp1 x >|< Comp1 y = Comp1 (x >|< y)
instance DisjunctiveMonoid (f p) => DisjunctiveMonoid (M1 i c f p) where
  falseP = M1 falseP
  M1 x >|< M1 y = M1 (x >|< y)
instance DisjunctiveMonoid (f p) => DisjunctiveMonoid (Rec1 f p) where
  falseP = Rec1 falseP
  Rec1 x >|< Rec1 y = Rec1 (x >|< y)
instance DisjunctiveMonoid c => DisjunctiveMonoid (K1 i c p) where
  falseP = K1 falseP
  K1 x >|< K1 y = K1 (x >|< y)
instance DisjunctiveMonoid p => DisjunctiveMonoid (Par1 p) where
  falseP = Par1 falseP
  Par1 x >|< Par1 y = Par1 (x >|< y)
instance BooleanAlgebra (U1 p) where
  trueP = U1
  notP _ = U1
  _ >&< _ = U1
instance (BooleanAlgebra (f p), BooleanAlgebra (g p))
  => BooleanAlgebra ((f :*: g) p) where
    trueP = trueP :*: trueP
    notP (x :*: y) = notP x :*: notP y
    (x0 :*: y0) >&< (x1 :*: y1) = (x0 >&< x1) :*: (y0 >&< y1)
instance BooleanAlgebra (f (g p)) => BooleanAlgebra ((f :.: g) p) where
  trueP = Comp1 trueP
  notP (Comp1 x) = Comp1 (notP x)
  Comp1 x >&< Comp1 y = Comp1 (x >&< y)
instance BooleanAlgebra (f p) => BooleanAlgebra (M1 i c f p) where
  trueP = M1 trueP
  notP (M1 x) = M1 (notP x)
  M1 x >&< M1 y = M1 (x >&< y)
instance BooleanAlgebra (f p) => BooleanAlgebra (Rec1 f p) where
  trueP = Rec1 trueP
  notP (Rec1 x) = Rec1 (notP x)
  Rec1 x >&< Rec1 y = Rec1 (x >&< y)
instance BooleanAlgebra c => BooleanAlgebra (K1 i c p) where
  trueP = K1 trueP
  notP (K1 x) = K1 (notP x)
  K1 x >&< K1 y = K1 (x >&< y)
instance BooleanAlgebra p => BooleanAlgebra (Par1 p) where
  trueP = Par1 trueP
  notP (Par1 x) = Par1 (notP x)
  Par1 x >&< Par1 y = Par1 (x >&< y)
instance KleeneStarAlgebra (U1 p) where
  starK _ = U1
instance (KleeneStarAlgebra (f p), KleeneStarAlgebra (g p))
  => KleeneStarAlgebra ((f :*: g) p) where
    starK (x :*: y) = starK x :*: starK y
    plusK (x :*: y) = plusK x :*: plusK y
    optK (x :*: y) = optK x :*: optK y
instance KleeneStarAlgebra (f (g p)) => KleeneStarAlgebra ((f :.: g) p) where
  starK (Comp1 x) = Comp1 (starK x)
  plusK (Comp1 x) = Comp1 (plusK x)
  optK (Comp1 x) = Comp1 (optK x)
instance KleeneStarAlgebra (f p) => KleeneStarAlgebra (M1 i c f p) where
  starK (M1 x) = M1 (starK x)
  plusK (M1 x) = M1 (plusK x)
  optK (M1 x) = M1 (optK x)
instance KleeneStarAlgebra (f p) => KleeneStarAlgebra (Rec1 f p) where
  starK (Rec1 x) = Rec1 (starK x)
  plusK (Rec1 x) = Rec1 (plusK x)
  optK (Rec1 x) = Rec1 (optK x)
instance KleeneStarAlgebra c => KleeneStarAlgebra (K1 i c p) where
  starK (K1 x) = K1 (starK x)
  plusK (K1 x) = K1 (plusK x)
  optK (K1 x) = K1 (optK x)
instance KleeneStarAlgebra p => KleeneStarAlgebra (Par1 p) where
  starK (Par1 x) = Par1 (starK x)
  plusK (Par1 x) = Par1 (plusK x)
  optK (Par1 x) = Par1 (optK x)
instance (Generic a, DisjunctiveMonoid (Rep a ()))
  => DisjunctiveMonoid (Generically a) where
    falseP = Generically (to (falseP :: Rep a ()))
    Generically x >|< Generically y =
      Generically (to (from x >|< from y :: Rep a ()))
instance (Generic a, BooleanAlgebra (Rep a ()))
  => BooleanAlgebra (Generically a) where
    trueP = Generically (to (trueP :: Rep a ()))
    notP (Generically x) = Generically (to (notP (from x :: Rep a ())))
    Generically x >&< Generically y =
      Generically (to (from x >&< from y :: Rep a ()))
instance (Generic a, Monoid (Rep a ()), KleeneStarAlgebra (Rep a ()))
  => KleeneStarAlgebra (Generically a) where
    starK (Generically x) = Generically (to (starK (from x :: Rep a ())))
    plusK (Generically x) = Generically (to (plusK (from x :: Rep a ())))
    optK (Generically x) = Generically (to (optK (from x :: Rep a ())))
instance (Generic1 f, DisjunctiveMonoid (Rep1 f a))
  => DisjunctiveMonoid (Generically1 f a) where
    falseP = Generically1 (to1 (falseP :: Rep1 f a))
    Generically1 x >|< Generically1 y =
      Generically1 (to1 (from1 x >|< from1 y :: Rep1 f a))
instance DisjunctiveMonoid (m b) => DisjunctiveMonoid (Kleisli m a b) where
  falseP = Kleisli falseP
  Kleisli f >|< Kleisli g = Kleisli (f >|< g)
instance DisjunctiveMonoid (f b) => DisjunctiveMonoid (Star f a b) where
  falseP = Star falseP
  Star f >|< Star g = Star (f >|< g)
instance DisjunctiveMonoid r => DisjunctiveMonoid (Forget r a b) where
  falseP = Forget falseP
  Forget f >|< Forget g = Forget (f >|< g)
instance ArrowPlus p => DisjunctiveMonoid (Pro.WrappedArrow p a b) where
  falseP = Pro.WrapArrow zeroArrow
  Pro.WrapArrow x >|< Pro.WrapArrow y = Pro.WrapArrow (x <+> y)
instance (Applicative f, DisjunctiveMonoid (p a b))
  => DisjunctiveMonoid (Cayley f p a b) where
    falseP = Cayley (pure falseP)
    Cayley x >|< Cayley y = Cayley (liftA2 (>|<) x y)
instance (DisjunctiveMonoid (p a b), DisjunctiveMonoid (q a b))
  => DisjunctiveMonoid (Bifunctor.Product p q a b) where
    falseP = Bifunctor.Pair falseP falseP
    Bifunctor.Pair x0 y0 >|< Bifunctor.Pair x1 y1 =
      Bifunctor.Pair (x0 >|< x1) (y0 >|< y1)
instance Alternative f => DisjunctiveMonoid (Joker f a b) where
  falseP = Joker empty
  Joker x >|< Joker y = Joker (x <|> y)
instance DisjunctiveMonoid (p a (f b)) => DisjunctiveMonoid (WrappedPafb f p a b) where
  falseP = WrapPafb falseP
  WrapPafb x >|< WrapPafb y = WrapPafb (x >|< y)
instance (Profunctor p, DisjunctiveMonoid (p a b))
  => DisjunctiveMonoid (Yoneda p a b) where
    falseP = proreturn falseP
    x >|< y = proreturn (proextract x >|< proextract y)
instance (Profunctor p, DisjunctiveMonoid (p a b))
  => DisjunctiveMonoid (Coyoneda p a b) where
    falseP = proreturn falseP
    x >|< y = proreturn (proextract x >|< proextract y)
