{- |
Module      : Control.Lens.Prismoid
Description : prismoids
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Control.Lens.Prismoid
  ( -- * Prismoid
    Prismoid
  , APrismoid
  , Prismatoid (..), runPrismatoid
  , Prismocular (..), runPrismocular, prismocular, withPrismocular
    -- * Combinators
  , prismoid
  , withPrismoid
  , clonePrismoid
  , mapPrismoid
  , somed
  , opted
  , lefted
  , righted
  , chained1
  , chained
  , intercalated
  , operated
  , separated
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.Internal.Profunctor
import Control.Lens.PartialIso
import Data.Monoid.Disjunctive (DisjunctiveMonoid (..))
import Data.Profunctor.Distributor
import Data.Profunctor.Monoidal ((>*), (*<), replicateP)
import Data.Profunctor.Monoidal.Cocartesian
import Data.Traversable.Homogeneous
import Data.Void
import GHC.Generics (Par1 (..), U1 (..), V1, (:*:) (..), (:+:) (..), (:.:) (..))

-- $setup
-- >>> import Control.Applicative (empty)
-- >>> import Control.Lens (Prism', prism')
-- >>> import Data.Bifunctor.Joker
-- >>> import Data.Char (digitToInt, isDigit)
-- >>> import Data.Functor.Identity (Identity (..))
-- >>> import Data.Profunctor.Distributor (Assoc (..), Operator (..), noSep, sepBy)
-- >>> import Text.ParserCombinators.ReadP (ReadP, char, readP_to_S, satisfy)

{- | `Prismoid`s generalize `Control.Lens.Prism.Prism`s
& `Control.Lens.Diopter.Diopter`s, combining them,
matching partially forwards, into a `Homogeneous` shape,
& building totally backwards.

`Control.Lens.Prism.Prism` ∪ `Control.Lens.Diopter.Diopter`
⊂ `Prismoid` ⊂ `Control.Lens.Bifocal.Bifocal`.

A `Prismoid` fails by its `Alternator`, never by its `Applicative` @f@,
so a `Control.Lens.Prism.Prism`, as a `Prismoid`, fails on a mismatch,
rather than passing it through, by the laws of
`Data.Profunctor.Monoidal.Cocartesian.CocartesianChoice`,
as rebuilding it from its partial functions,
by `Control.Lens.PartialIso.withPartialIso` & `Control.Lens.PartialIso.partialIso`,
makes it do in any `Choice`.
A `Control.Lens.Bifocal.Bifocal` adds failing backwards, by a `Witherable.Filterable` @f@.

`Prismoid`s are isomorphic to t'Prismatoid's,
by `Homogeneous` shapes, & to t'Prismocular's, by partial probes.
-}
type Prismoid s t a b = forall p f.
  (Alternator p, Applicative f)
    => p a (f b) -> p s (f t)

{- | `APrismoid` is monomorphically a `Prismoid`.

> prop> Prismoid s t a b ⊂ APrismoid s t a b
-}
type APrismoid s t a b =
  Prismatoid a b a (Identity b) -> Prismatoid a b s (Identity t)

{- | Build a `Prismoid` from its partial match forwards, into a
`Homogeneous` shape, & its total build backwards.

>>> withPrismoid (prismoid (\xs -> if null xs then Nothing else Just xs) id) $ \f _ -> (length <$> f "", length <$> f "ab")
(Nothing,Just 2)
-}
prismoid
  :: Homogeneous h
  => (s -> Maybe (h a)) -> (h b -> t) -> Prismoid s t a b
prismoid f g = unwrapPafb . runPrismatoid (Prismatoid f g) . WrapPafb

{- | Action of `APrismoid` on `Alternator`s. -}
mapPrismoid :: Alternator p => APrismoid s t a b -> p a b -> p s t
mapPrismoid pat = withPrismoid pat $ \f g -> runPrismatoid (Prismatoid f g)

{- | Clone `APrismoid` so that you can reuse the same
monomorphically typed `Prismoid` for different purposes.
-}
clonePrismoid :: APrismoid s t a b -> Prismoid s t a b
clonePrismoid pat = withPrismoid pat prismoid

{- | Convert `APrismoid` to the pair of functions that characterize it.

>>> withPrismoid somed $ \f _ -> (fmap length (f ""), fmap length (f "ab"))
(Nothing,Just 2)
-}
withPrismoid
  :: APrismoid s t a b
  -> (forall h. Homogeneous h => (s -> Maybe (h a)) -> (h b -> t) -> r)
  -> r
withPrismoid pat k =
  case runIdentity <$> pat (Identity <$> Prismatoid (Just . Par1) unPar1) of
    Prismatoid f g -> k f g

{- | One or more, like `someP`. -}
somed :: Prismoid [a] [b] a b
somed = unwrapPafb . someP . WrapPafb

{- | Exactly some number of times, like
`Data.Profunctor.Monoidal.replicateP`,
or, `separated` by a t'SepBy', like `intercalateP`. -}
intercalated :: (AsEmpty s, Cons s s a a) => Int -> Prismoid s s a a
intercalated n = unwrapPafb . replicateP n . WrapPafb

{- | An expression of `Operator`s, from a table of them, ordered from
highest to lowest precedence, like `withOperators`. An operator table,
like a t'SepBy', is of an `Alternator` @p@, its symbols data-free.

>>> :{
data Sum = Digit Int | Plus Sum Sum deriving Show
_Plus :: Prism' Sum (Sum, Sum)
_Plus = prism' (uncurry Plus) (\case Plus x y -> Just (x, y); _ -> Nothing)
:}

>>> let plus = Infix LeftAssoc _Plus (Joker (() <$ char '+'))
>>> let digit = Joker (Digit . digitToInt <$> satisfy isDigit)
>>> [e | (e, "") <- readP_to_S (runJoker (operated [[plus]] digit)) "1+2+3"]
[Plus (Plus (Digit 1) (Digit 2)) (Digit 3)]
-}
operated :: Alternator p => [[Operator p a b]] -> p a b -> p a b
operated = withOperators

{- | One or zero with default. -}
opted :: APrism a b () () -> Prismoid a b a b
opted def = unwrapPafb . optionP def . WrapPafb

{- | `lefted` is like `_Left`, except
with heterogeneous `Right` parameters. -}
lefted :: Prismoid (Either a c) (Either b d) a b
lefted = unwrapPafb . alternate . Left . WrapPafb


{- | `righted` is like `_Right`, except
with heterogeneous `Left` parameters. -}
righted :: Prismoid (Either c a) (Either d b) a b
righted = unwrapPafb . alternate . Right . WrapPafb

{- |
Associate a binary constructor pattern to sequence one or more times,
like `chain1`, or, `separated` by a t'SepBy', with separators.
-}
chained1
  :: (forall x. x -> Either x x)
  -> APartialIso a b (a,a) (b,b)
  -> Prismoid a b a b
chained1 assoc binPat =
  unwrapPafb . chain1 assoc binPat noSep . WrapPafb

{- |
Associate a binary constructor pattern to sequence one or more times,
or use a nilary constructor pattern to sequence zero times,
like `chain`, or, `separated` by a t'SepBy', with separators.
-}
chained
  :: (forall x. x -> Either x x)
  -> APartialIso a b (a,a) (b,b)
  -> APrism a b () ()
  -> Prismoid a b a b
chained assoc binPat nilPat =
  unwrapPafb . chain assoc binPat nilPat noSep . WrapPafb

{- | A t'Prismatoid' provides efficient access
to the pair of functions that make up a `Prismoid`,
like a t'Control.Lens.Diopter.Dioptrice' which may fail to match.
-}
data Prismatoid a b s t where
  Prismatoid
    :: Homogeneous h
    => (s -> Maybe (h a))
    -> (h b -> t)
    -> Prismatoid a b s t
instance Profunctor (Prismatoid a b) where
  dimap f' g' (Prismatoid f g) = Prismatoid (f . f') (g' . g)
instance Functor (Prismatoid a b s) where fmap = rmap
instance Applicative (Prismatoid a b s) where
  pure t = Prismatoid (const (Just U1)) (const t)
  liftA2 h (Prismatoid f0 g0) (Prismatoid f1 g1) = Prismatoid
    (\s -> liftA2 (:*:) (f0 s) (f1 s))
    (\(x :*: y) -> h (g0 x) (g1 y))
  (<*>) = liftA2 id
instance Alternative (Prismatoid a b s) where
  empty = Prismatoid (const Nothing) (\(v :: V1 b) -> case v of {})
  Prismatoid f0 g0 <|> Prismatoid f1 g1 = Prismatoid
    (\s -> (L1 <$> f0 s) <|> (R1 <$> f1 s))
    (\case {L1 x -> g0 x; R1 y -> g1 y})
instance DisjunctiveMonoid (Prismatoid a b s t)
instance CocartesianMonoidal (Prismatoid a b) where
  zeroP = Prismatoid absurd (\(v :: V1 b) -> case v of {})
  Prismatoid f0 g0 >+< Prismatoid f1 g1 = Prismatoid
    (either (fmap L1 . f0) (fmap R1 . f1))
    (\case {L1 x -> Left (g0 x); R1 y -> Right (g1 y)})
instance Choice (Prismatoid a b) where
  left' = alternate . Left
  right' = alternate . Right
instance CocartesianChoice (Prismatoid a b) where
  alternate = \case
    Left (Prismatoid f g) -> Prismatoid (either f (const Nothing)) (Left . g)
    Right (Prismatoid f g) -> Prismatoid (either (const Nothing) f) (Right . g)
instance Distributor (Prismatoid a b) where
  optionalP (Prismatoid f g) =
    Prismatoid (fmap Comp1 . traverse f) (fmap g . unComp1)
  manyP (Prismatoid f g) =
    Prismatoid (fmap Comp1 . traverse f) (fmap g . unComp1)
instance Alternator (Prismatoid a b)

{- | Run a t'Prismatoid' on an `Alternator`,
failing by `falseP` where it doesn't match. -}
runPrismatoid :: Alternator p => Prismatoid a b s t -> p a b -> p s t
runPrismatoid (Prismatoid f g) p =
  dialt (maybe (Left ()) Right . f) id g falseP (homogeneously p)

{- | t'Prismocular' is a secondary concrete representation of `Prismoid`s,
by partial probes of a source, run in an `Alternative`,
as a t'Control.Lens.Bifocal.Binocular' is of
`Control.Lens.Bifocal.Bifocal`s, without filtering.
-}
newtype Prismocular a b s t = Prismocular
  { unPrismocular
      :: forall f. Alternative f => ((s -> Maybe a) -> f b) -> f t
  }
instance Profunctor (Prismocular a b) where
  dimap f g (Prismocular k) = Prismocular $ fmap g . k . (. (. f))
instance Functor (Prismocular a b s) where fmap = rmap
instance Applicative (Prismocular a b s) where
  pure t = Prismocular (pure (pure t))
  Prismocular x <*> Prismocular y = Prismocular (liftA2 (<*>) x y)
instance Alternative (Prismocular a b s) where
  empty = Prismocular (pure empty)
  Prismocular x <|> Prismocular y = Prismocular (liftA2 (<|>) x y)
  many = lmap repeat . manyP
  some = lmap repeat . someP
instance DisjunctiveMonoid (Prismocular a b s t)
instance Choice (Prismocular a b) where
  left' = alternate . Left
  right' = alternate . Right
instance CocartesianMonoidal (Prismocular a b)
instance CocartesianChoice (Prismocular a b) where
  alternate = \case
    Left (Prismocular k) -> Prismocular $
      fmap Left . k . (. (\f -> either f (const Nothing)))
    Right (Prismocular k) -> Prismocular $
      fmap Right . k . (. (\f -> either (const Nothing) f))
instance Distributor (Prismocular a b)
instance Alternator (Prismocular a b)

{- | Run a t'Prismocular' on an `Alternator`,
failing by `falseP` where a probe doesn't match. -}
runPrismocular :: Alternator p => Prismocular a b s t -> p a b -> p s t
runPrismocular (Prismocular k) p =
  k $ \probe -> dialt (maybe (Left ()) Right . probe) id id falseP p

{- | Build a `Prismoid` from a t'Prismocular'. -}
prismocular :: Prismocular a b s t -> Prismoid s t a b
prismocular pm = unwrapPafb . runPrismocular pm . WrapPafb

{- | Run `APrismoid` by partial probes in an `Alternative`.

>>> withPrismocular somed (\probe -> maybe empty pure (probe "")) :: Maybe String
Nothing
>>> withPrismocular somed (\probe -> maybe empty pure (probe "ab")) :: Maybe String
Just "ab"
-}
withPrismocular
  :: Alternative g
  => APrismoid s t a b -> ((s -> Maybe a) -> g b) -> g t
withPrismocular pat = unPrismocular (mapPrismoid pat (Prismocular ($ Just)))

{- | Action of `APrismoid` on `Alternator`s, like `mapPrismoid`,
with a t'SepBy', its separator
between consecutive foci, & its delimiters around them all.
A shape of @n@ foci gets @n - 1@ separators, like `Data.List.intersperse`.

> prop> separated pat noSep = clonePrismoid pat
> prop> separated pat (SepBy beg end sep) p = beg >* separated pat (sepBy sep) p *< end
> prop> separated somed = several1
> prop> separated manied = several
> prop> separated (intercalated n) = intercalateP n
> prop> separated (chained1 assoc pat) = chain1 assoc pat

>>> let digits = runJoker (separated somed (sepBy (Joker (() <$ char ','))) (Joker (satisfy isDigit)) :: Joker ReadP String String)
>>> [ds | (ds, "") <- readP_to_S digits "1,2,3"]
["123"]
-}
separated
  :: Alternator p
  => APrismoid s t a b -> SepBy (p () ()) -> p a b -> p s t
separated pat (SepBy beg end sep) p =
  case mapPrismoid pat (Interspersing empty p (sep >* p)) of
    Interspersing noFoci firstFoci _ -> beg >* (noFoci <|> firstFoci) *< end

{- | An `Alternator` which separates the foci it sequences,
from either of two states: before any focus, or after one.
Before any focus, an action either sequences no focus,
or some, its first unseparated; after one, it separates every focus.
Those are its three fields, in order.
-}
data Interspersing p a b = Interspersing (p a b) (p a b) (p a b)
instance Profunctor p => Profunctor (Interspersing p) where
  dimap f g ~(Interspersing n x y) = Interspersing (dimap f g n) (dimap f g x) (dimap f g y)
instance Alternator p => Functor (Interspersing p a) where fmap = rmap
instance Alternator p => Applicative (Interspersing p a) where
  pure b = Interspersing (pure b) empty (pure b)
  liftA2 h ~(Interspersing xn xf xl) ~(Interspersing yn yf yl) = Interspersing
    (liftA2 h xn yn)
    (liftA2 h xn yf <|> liftA2 h xf yl)
    (liftA2 h xl yl)
instance Alternator p => Alternative (Interspersing p a) where
  empty = Interspersing empty empty empty
  ~(Interspersing xn xf xl) <|> ~(Interspersing yn yf yl) =
    Interspersing (xn <|> yn) (xf <|> yf) (xl <|> yl)
instance Alternator p => DisjunctiveMonoid (Interspersing p a b)
instance Alternator p => Choice (Interspersing p) where
  left' = alternate . Left
  right' = alternate . Right
instance Alternator p => CocartesianMonoidal (Interspersing p) where
  zeroP = Interspersing zeroP zeroP zeroP
  ~(Interspersing xn xf xl) >+< ~(Interspersing yn yf yl) =
    Interspersing (xn >+< yn) (xf >+< yf) (xl >+< yl)
instance Alternator p => CocartesianChoice (Interspersing p) where
  alternate = \case
    Left ~(Interspersing n x y) ->
      Interspersing (alternate (Left n)) (alternate (Left x)) (alternate (Left y))
    Right ~(Interspersing n x y) ->
      Interspersing (alternate (Right n)) (alternate (Right x)) (alternate (Right y))
instance Alternator p => Distributor (Interspersing p)
instance Alternator p => Alternator (Interspersing p)
