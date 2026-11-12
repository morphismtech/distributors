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
    -- * Combinators
  , prismoid
  , withPrismoid
  , clonePrismoid
  , mapPrismoid
  , somed
  , opted
  , lefted
  , righted
    -- * Plasmoid
  , Plasmoid
  , chained1
  , chained
  , severaled
  , severaled1
  , intercalated
  , operated
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.Internal.Profunctor
import Control.Lens.PartialIso
import Data.Monoid.Disjunctive (DisjunctiveMonoid (..))
import Data.Profunctor.Distributor
import Data.Profunctor.Monoidal.Cocartesian
import Data.Traversable.Homogeneous
import Data.Void
import GHC.Exts (IsList (..))
import GHC.Generics (Par1 (..), U1 (..), V1, (:*:) (..), (:+:) (..), (:.:) (..))

-- $setup
-- >>> import Control.Lens (Prism', prism')
-- >>> import Data.Bifunctor.Joker
-- >>> import Data.Char (digitToInt, isDigit)
-- >>> import Data.Functor.Identity (Identity (..))
-- >>> import Data.Profunctor.Distributor (Assoc (..), Operator (..), noSep, sepBy)
-- >>> import Text.ParserCombinators.ReadP (ReadP, char, readP_to_S, satisfy)

{- | `Prismoid`s generalize `Control.Lens.Prism.Prism`s
& `Control.Lens.Diopter.Diopter`s, combining them,
matching partially forwards, into a `Homogeneous` shape,
& building totally backwards. Writing ⊂ for "every one is a",

`Control.Lens.Prism.Prism` ∪ `Control.Lens.Diopter.Diopter`
⊂ `Prismoid` ⊂ `Control.Lens.Bifocal.Bifocal`.

A `Prismoid` fails by its `Alternator`, never by its `Applicative` @f@,
so a `Control.Lens.Prism.Prism`, as a `Prismoid`, fails on a mismatch,
rather than passing it through, by the laws of
`Data.Profunctor.Monoidal.Cocartesian.CocartesianChoice`,
as `Control.Lens.PartialIso.clonePartialIso` makes it do in any `Choice`.
A `Control.Lens.Bifocal.Bifocal` adds failing backwards, by a `Witherable.Filterable` @f@.

`Prismoid`s are isomorphic to t'Prismatoid's.
-}
type Prismoid s t a b = forall p f.
  (Alternator p, Applicative f)
    => p a (f b) -> p s (f t)

{- | A `Plasmoid` is a family of optics, separated by a t'SepBy',
which is an optic at the `Alternator` @p@ of its separators.

Its separators are data-free, @p () ()@, so they place effects
between its foci, but never change what its source or target holds.
So without separators, by `noSep`, which is polymorphic in @p@,
a `Plasmoid` is a `Prismoid`, & its data is that `Prismoid`'s;
for any @plasmoid :: Plasmoid s t a b@,
@plasmoid noSep :: Prismoid s t a b@.

>>> withPrismoid (severaled1 noSep :: Prismoid String String Char Char) $ \f _ -> fmap length (f "abc")
Just 3
-}
type Plasmoid s t a b = forall p f.
  (Alternator p, Applicative f)
    => SepBy (p () ()) -> p a (f b) -> p s (f t)

{- | `APrismoid` is monomorphically a `Prismoid`. -}
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

{- | Zero or more, separated by a t'SepBy', like `several`. -}
severaled :: (IsList s, IsList t) => Plasmoid s t (Item s) (Item t)
severaled sep = unwrapPafb . several (fmap (WrapPafb . rmap pure) sep) . WrapPafb

{- | One or more, separated by a t'SepBy', like `several1`.

>>> let digits = runJoker (severaled1 (sepBy (Joker (() <$ char ','))) (Joker (Identity <$> satisfy isDigit)) :: Joker ReadP String (Identity String))
>>> [ds | (Identity ds, "") <- readP_to_S digits "1,2,3"]
["123"]
-}
severaled1 :: (IsList s, IsList t) => Plasmoid s t (Item s) (Item t)
severaled1 sep = unwrapPafb . several1 (fmap (WrapPafb . rmap pure) sep) . WrapPafb

{- | Exactly some number of times, separated by a t'SepBy',
like `intercalateP`, or without separators, by `noSep`, like
`Data.Profunctor.Monoidal.replicateP`. -}
intercalated :: (AsEmpty s, Cons s s a a) => Int -> Plasmoid s s a a
intercalated n sep =
  unwrapPafb . intercalateP n (fmap (WrapPafb . rmap pure) sep) . WrapPafb

{- | An expression of `Operator`s, from a table of them, ordered from
highest to lowest precedence, like `withOperators`. An operator table,
like a t'SepBy', is of an `Alternator` @p@, its symbols data-free.

>>> :{
data Sum = Digit Int | Plus Sum Sum deriving Show
_Plus :: Prism' Sum (Sum, Sum)
_Plus = prism' (uncurry Plus) (\case Plus x y -> Just (x, y); _ -> Nothing)
:}

>>> let plus = Infix LeftAssoc _Plus (Joker (() <$ char '+'))
>>> let digit = Joker (Identity . Digit . digitToInt <$> satisfy isDigit)
>>> [e | (Identity e, "") <- readP_to_S (runJoker (operated [[plus]] digit)) "1+2+3"]
[Plus (Plus (Digit 1) (Digit 2)) (Digit 3)]
-}
operated
  :: (Alternator p, Applicative f)
  => [[Operator p a b]] -> p a (f b) -> p a (f b)
operated table =
  unwrapPafb . withOperators (map (map wrapping) table) . WrapPafb
  where
    wrapping = \case
      Infix assoc pat sym -> Infix assoc pat (WrapPafb (rmap pure sym))
      Prefix pat sym -> Prefix pat (WrapPafb (rmap pure sym))
      Postfix pat sym -> Postfix pat (WrapPafb (rmap pure sym))

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
Associate a binary constructor pattern to sequence one or more times.
-}
chained1
  :: (forall x. x -> Either x x)
  -> APartialIso a b (a,a) (b,b)
  -> Plasmoid a b a b
chained1 assoc binPat sep =
  unwrapPafb . chain1 assoc binPat (fmap (WrapPafb . rmap pure) sep) . WrapPafb

{- |
Associate a binary constructor pattern to sequence one or more times,
or use a nilary constructor pattern to sequence zero times.
-}
chained
  :: (forall x. x -> Either x x)
  -> APartialIso a b (a,a) (b,b)
  -> APrism a b () ()
  -> Plasmoid a b a b
chained assoc binPat nilPat sep =
  unwrapPafb . chain assoc binPat nilPat (fmap (WrapPafb . rmap pure) sep) . WrapPafb

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
