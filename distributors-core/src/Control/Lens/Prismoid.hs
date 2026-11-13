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
    -- * Applicators
  , (>?*)
  , sepBy
  , withOperators
    -- * Combinators
  , prismoid
  , withPrismoid
  , clonePrismoid
  , opted
  , lefted
  , righted
  , chain1
  , chain
  , exactly
  , atLeast
  , atMost
  , inRange
    -- * Operator Expressions
  , Operator (..)
  , Assoc (..)
  ) where

import Control.Applicative
import Control.Monad (void)
import Data.Maybe (fromMaybe, isJust)
import Control.Lens
import Control.Lens.Internal.Profunctor
import Control.Lens.PartialIso
import Data.Monoid.Disjunctive (DisjunctiveMonoid (..), orP)
import Data.Profunctor.Distributor
import Data.Profunctor.Monoidal
import Data.Profunctor.Monoidal.Cocartesian
import Data.Profunctor.Unsafe ((#.))
import Data.Traversable.Homogeneous
import Data.Void
import GHC.Generics (Par1 (..), U1 (..), V1, (:*:) (..), (:+:) (..), (:.:) (..))

-- $setup
-- >>> import Control.Applicative (empty)
-- >>> import Control.Lens (Prism', prism')
-- >>> import Data.Bifunctor.Joker
-- >>> import Data.Char (digitToInt, isDigit)
-- >>> import Control.Lens.Monocle (ditraversed)
-- >>> import Data.Functor.Identity (Identity (..))
-- >>> import Data.Functor.Product (Product (..))
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

{- | Action of a `Prismoid` on `Alternator`s,
applying it directly at the `Alternator`, without converting it
to a concrete form, so the `Alternator`'s own methods,
like `someP` & `optionP`, act as they are.

> prop> prsm >?* p = prsm >? p
> prop> atLeast 1 >?* p = someP p
> prop> opted def >?* p = optionP def p

So a `Prismoid` acts on an `Alternative`, by t'Joker',
as a homomorphism, @atLeast 1@ to `some`, @several@ to `many`,
& @opted@ to `optional`; & on a `Data.Monoid.Disjunctive.KleeneStarAlgebra`,
by @Data.Profunctor.Grammar.Grammor@, @atLeast 1@ to `plusK`,
@several@ to `starK` & @opted@ to `optK`.

>>> let digits = runJoker (atLeast 1 >?* Joker (satisfy isDigit)) :: ReadP String
>>> [ds | (ds, "") <- readP_to_S digits "123"]
["123"]
-}
(>?*) :: Alternator p => Prismoid s t a b -> p a b -> p s t
pat >?* p = runIdentity #. pat (Identity #. p)
infixl 4 >?*

{- | Clone `APrismoid` so that you can reuse the same
monomorphically typed `Prismoid` for different purposes.
-}
clonePrismoid :: APrismoid s t a b -> Prismoid s t a b
clonePrismoid pat = withPrismoid pat prismoid

{- | Convert `APrismoid` to the pair of functions that characterize it.

>>> withPrismoid (atLeast 1) $ \f _ -> (fmap length (f ""), fmap length (f "ab"))
(Nothing,Just 2)
-}
withPrismoid
  :: APrismoid s t a b
  -> (forall h. Homogeneous h => (s -> Maybe (h a)) -> (h b -> t) -> r)
  -> r
withPrismoid pat k =
  case runIdentity <$> pat (Identity <$> Prismatoid (Just . Par1) unPar1) of
    Prismatoid f g -> k f g

{- | Exactly some number of times, or separated by `sepBy`.

> prop> exactly n = inRange n (Just n)
> prop> exactly n >?* p = replicateP n p
-}
exactly :: Int -> Prismoid [a] [b] a b
exactly n = inRange n (Just n)

{- | At least some number of times, or separated by `sepBy`,
ending with the `Alternator`'s own `someP`, or, for at least none,
its own `manyP`.

> prop> atLeast n = inRange n Nothing
> prop> atLeast 0 = several
> prop> atLeast 1 >?* p = someP p

>>> let digits n = runJoker (atLeast n >?* Joker (satisfy isDigit)) :: ReadP String
>>> [ds | (ds, "") <- readP_to_S (digits 2) "123"]
["123"]
>>> [ds | (ds, "") <- readP_to_S (digits 2) "1"]
[]
-}
atLeast :: Int -> Prismoid [a] [b] a b
atLeast n = inRange n Nothing

{- | At most some number of times, trying more first,
or separated by `sepBy`.

> prop> atMost n = inRange 0 (Just n)

>>> let digits n = runJoker (atMost n >?* Joker (satisfy isDigit)) :: ReadP String
>>> [ds | (ds, "") <- readP_to_S (digits 2) "12"]
["12"]
>>> [ds | (ds, "") <- readP_to_S (digits 2) "123"]
[]
-}
atMost :: Int -> Prismoid [a] [b] a b
atMost n = inRange 0 (Just n)

{- | Between some numbers of times, inclusive, at least a lower bound,
& at most an upper bound, if there's one, like a regular expression's
@{lo,hi}@, or @{lo,}@, or separated by `sepBy`.
It takes the mandatory times first, then, unbounded,
the `Alternator`'s own `someP` or `manyP`, or, bounded,
the optional times, trying more first.
It never matches where @lo > hi@.

>>> let digits lo hi = runJoker (inRange lo hi >?* Joker (satisfy isDigit)) :: ReadP String
>>> [ds | (ds, "") <- readP_to_S (digits 2 (Just 3)) "123"]
["123"]
>>> [ds | n <- [1 .. 4], (ds, "") <- readP_to_S (digits 2 (Just 3)) (take n "1234")]
["12","123"]
-}
inRange :: Int -> Maybe Int -> Prismoid [a] [b] a b
inRange lo hi = unwrapPafb . go lo hi . WrapPafb
  where
    go :: Alternator p => Int -> Maybe Int -> p a b -> p [a] [b]
    go l h p
      | maybe False (l >) h = empty
      | l > 1 || (l == 1 && isJust h) = p >:< go (l - 1) (subtract 1 <$> h) p
      | l == 1 = someP p
      | otherwise = case h of
          Nothing -> manyP p
          Just m
            | m <= 0 -> eotList . swapped >~ empty >+< oneP
            | otherwise -> eotList . swapped >~ p >*< go 0 (Just (m - 1)) p >+< oneP

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
`Left` or `Right` associated, folding & unfolding it by
`Control.Lens.PartialIso.difoldl` or `Control.Lens.PartialIso.difoldr`,
or separated by `sepBy`.
-}
chain1
  :: (forall x. x -> Either x x) -- ^ `Left` or `Right` associate
  -> APartialIso a b (a,a) (b,b) -- ^ binary constructor pattern
  -> Prismoid a b a b
chain1 assoc binPat = unwrapPafb . chainP . WrapPafb
  where
    chainP p = case assoc () of
      Left _ -> difoldl binPat >? p >*< manyP p
      Right _ -> difoldr binPat >? manyP p >*< p

{- |
Associate a binary constructor pattern to sequence one or more times,
or use a nilary constructor pattern to sequence zero times,
like `chain1` & `opted`,
or separated by `sepBy`.
-}
chain
  :: (forall x. x -> Either x x) -- ^ `Left` or `Right` associate
  -> APartialIso a b (a,a) (b,b) -- ^ binary constructor pattern
  -> APrism a b () () -- ^ nilary constructor pattern
  -> Prismoid a b a b
chain assoc binPat nilPat = opted nilPat . chain1 assoc binPat

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

>>> withPrismocular (atLeast 1) (\probe -> maybe empty pure (probe "")) :: Maybe String
Nothing
>>> withPrismocular (atLeast 1) (\probe -> maybe empty pure (probe "ab")) :: Maybe String
Just "ab"
-}
withPrismocular
  :: Alternative g
  => APrismoid s t a b -> ((s -> Maybe a) -> g b) -> g t
withPrismocular pat = unPrismocular (clonePrismoid pat >?* Prismocular ($ Just))

{- | Action of a `Prismoid` on `Alternator`s, like `>?*`,
with a separator between consecutive foci, data-free,
so a shape of @n@ foci gets @n - 1@ separators,
like `Data.List.intersperse`. Delimiters compose around it,
@beg >* sepBy sep pat p *< end@.
It applies the `Prismoid` directly, as `>?*` does, so the `Alternator`'s
own `manyP`, `someP`, `optionalP` & `optionP` sequence the foci,
by an upper triangular matrix of actions.
It prefers sequencing foci to sequencing none,
so a deterministic `Alternator` sequences them greedily.

> prop> sepBy oneP pat p = pat >?* p
> prop> sepBy sep (atLeast 1) p = p >:< manyP (sep >* p)
> prop> sepBy sep several p = p >:< manyP (sep >* p) <|> asEmpty

Separating `Control.Lens.Diopter.several`, `atLeast`, `atMost`, `inRange`,
`chain1`, `chain` or `exactly`, it sequences
lists, binary constructor patterns, or a number of repetitions;
& separating a `Control.Lens.Monocle.Monocle`, like
`Control.Lens.Monocle.ditraversed`, the positions of a fixed product.
Other `IsList`s act as lists by @`Control.Lens.PartialIso.listed` ~<@.

>>> let comma = Joker (() <$ char ',')
>>> let digit = Joker (satisfy isDigit)
>>> let digits = runJoker (sepBy comma (atLeast 1) digit) :: ReadP String
>>> [ds | (ds, "") <- readP_to_S digits "1,2,3"]
["123"]
>>> let pair = runJoker (sepBy comma ditraversed digit) :: ReadP (Product Identity Identity Char)
>>> [ds | (ds, "") <- readP_to_S pair "1,2"]
[Pair (Identity '1') (Identity '2')]
-}
sepBy
  :: Alternator p
  => p () () -> Prismoid s t a b -> p a b -> p s t
sepBy sep pat p =
  case pat >?* UpperTriangular Nothing p (sep >* p) of
    UpperTriangular noFoci firstFoci _ -> maybe firstFoci (firstFoci <|>) noFoci

{- | An upper triangular matrix of actions, @[n f; 0 l]@,
of transitions between two states, an `Alternator` by
matrix product `liftA2`, entrywise alternation `<|>`, & the star
@manyP [n f; 0 l] = [n*, n* f l*; 0, l*]@.

Its first entry is `Nothing` where it's zero statically,
so that the star of a matrix @[0 f; 0 l]@ is @f l*@.
Where it's an action, the star's @n* f l*@ is @`manyTillP` n (f l*)@,
which a static `Alternator`, like a `Control.Lens.Grammar.Grammor`,
defines without recursing.

`sepBy` separates foci by it, its states before any focus & after one:
before any focus, an action sequences no focus, @n@, or some, its first
unseparated, @f@; after one, it separates every focus, @l@.
Where both are possible, it prefers a focus to none, greedily.
-}
data UpperTriangular p a b = UpperTriangular (Maybe (p a b)) (p a b) (p a b)
instance Profunctor p => Profunctor (UpperTriangular p) where
  dimap f g ~(UpperTriangular n x y) =
    UpperTriangular (dimap f g <$> n) (dimap f g x) (dimap f g y)
instance Alternator p => Functor (UpperTriangular p a) where fmap = rmap
instance Alternator p => Applicative (UpperTriangular p a) where
  pure b = UpperTriangular (Just (pure b)) empty (pure b)
  liftA2 h ~(UpperTriangular xn xf xl) ~(UpperTriangular yn yf yl) = UpperTriangular
    (liftA2 (liftA2 h) xn yn)
    (maybe id (\n -> (<|> liftA2 h n yf)) xn (liftA2 h xf yl))
    (liftA2 h xl yl)
instance Alternator p => Alternative (UpperTriangular p a) where
  empty = UpperTriangular Nothing empty empty
  ~(UpperTriangular xn xf xl) <|> ~(UpperTriangular yn yf yl) =
    UpperTriangular (liftA2 (<|>) xn yn <|> xn <|> yn) (xf <|> yf) (xl <|> yl)
instance Alternator p => DisjunctiveMonoid (UpperTriangular p a b)
instance Alternator p => Choice (UpperTriangular p) where
  left' = alternate . Left
  right' = alternate . Right
instance Alternator p => CocartesianMonoidal (UpperTriangular p) where
  zeroP = UpperTriangular Nothing zeroP zeroP
  ~(UpperTriangular xn xf xl) >+< ~(UpperTriangular yn yf yl) = UpperTriangular
    ((fromMaybe empty xn >+< fromMaybe empty yn) <$ (void xn <|> void yn))
    (xf >+< yf)
    (xl >+< yl)
instance Alternator p => CocartesianChoice (UpperTriangular p) where
  alternate = \case
    Left ~(UpperTriangular n x y) -> UpperTriangular
      (alternate . Left <$> n) (alternate (Left x)) (alternate (Left y))
    Right ~(UpperTriangular n x y) -> UpperTriangular
      (alternate . Right <$> n) (alternate (Right x)) (alternate (Right y))
{- | Repetitions sequence by the `Alternator`'s own methods: with no foci,
or, after a focus, separating every focus. Before the first focus,
repetitions without foci may precede it. -}
instance Alternator p => Distributor (UpperTriangular p) where
  manyP ~(UpperTriangular n x y) =
    UpperTriangular (Just (manyP (fromMaybe empty n))) f (manyP y)
    where
      f = maybe id manyTillP n (x >:< manyP y)
  optionalP ~(UpperTriangular n x y) = UpperTriangular
    (Just (optionalP (fromMaybe empty n))) (_Just >? x) (optionalP y)
instance Alternator p => Alternator (UpperTriangular p) where
  someP i@(~(UpperTriangular n _ y)) = case manyP i of
    ~(UpperTriangular _ f _) -> UpperTriangular (someP <$> n) f (someP y)
  optionP def ~(UpperTriangular n x y) = UpperTriangular
    (Just (optionP def (fromMaybe empty n))) x (optionP def y)
  manyTillP ~(UpperTriangular n x y) ~(UpperTriangular n' x' y') =
    UpperTriangular (maybe id manyTillP n <$> n') f l
    where
      l = manyTillP y y'
      f = maybe id manyTillP n (x' <|> x >:< l)

{- | An operator at some level of an operator table, for use with
`withOperators`. `Infix` takes an `Assoc` to distinguish binary operators;
`Prefix` & `Postfix` are for unary operators. -}
data Operator p a b where
  Infix
    :: Assoc -- ^ `NonAssoc`, `LeftAssoc`, `RightAssoc`
    -> APrism a b (a,a) (b,b) -- ^ binary constructor pattern
    -> p () () -- ^ operator symbol
    -> Operator p a b
  Prefix
    :: APrism a b a b -- ^ unary constructor pattern
    -> p () () -- ^ operator symbol
    -> Operator p a b
  Postfix
    :: APrism a b a b -- ^ unary constructor pattern
    -> p () () -- ^ operator symbol
    -> Operator p a b

{- | The associativity of an `Infix` binary operator. -}
data Assoc = NonAssoc | LeftAssoc | RightAssoc
  deriving stock (Eq, Ord, Show, Read)

{- | Build an expression `Alternator` from a table of `Operator`s and
an atomic term `Alternator`, analogous to @buildExpressionParser@ from
[parsec](https://hackage.haskell.org/package/parsec).

The operator table is a list of list of operators, ordered from highest to lowest precedence.
Each level is a list of `Operator`s which share precedence.
Within a level, `Infix` takes an `Assoc` to set left, right or non-associativity for binary operators,
while `Prefix` & `Postfix` are for unary operators.

Its operator symbols are actions of the `Alternator` @p@, data-free,
so, unlike a `Prismoid`, it isn't polymorphic in @p@.

>>> :{
data Sum = Digit Int | Plus Sum Sum deriving Show
_Plus :: Prism' Sum (Sum, Sum)
_Plus = prism' (uncurry Plus) (\case Plus x y -> Just (x, y); _ -> Nothing)
:}

>>> let plus = Infix LeftAssoc _Plus (Joker (() <$ char '+'))
>>> let digit = Joker (Digit . digitToInt <$> satisfy isDigit)
>>> [e | (e, "") <- readP_to_S (runJoker (withOperators [[plus]] digit)) "1+2+3"]
[Plus (Plus (Digit 1) (Digit 2)) (Digit 3)]

For a larger example, see the expression grammar in "Control.Lens.Grammar",
of natural numbers with postfix, right-associative & left-associative operators.
-}
withOperators
  :: Alternator p
  => [[Operator p a b]] -- ^ operator table
  -> p a b -- ^ atomic term
  -> p a b -- ^ expression
withOperators table p = foldl makeLevel p table
  where
    makeLevel term ops =
      let
        (infixes, pres, posts) = foldr splitOp ([],[],[]) ops
        termP = withPostP posts (withPreP pres term)
      in
        infixP infixes termP

    splitOp oper (infixes, pres, posts) = case oper of
      Infix associativity pat sym -> ((associativity,pat,sym):infixes, pres, posts)
      Prefix pat sym -> (infixes, (pat,sym):pres, posts)
      Postfix pat sym -> (infixes, pres, (pat,sym):posts)

    tagSepP syms = orP [only i >? sym | (i, sym) <- zip [0 :: Int ..] syms]

    withPreP ops inner =
      difoldr (taggedP (,) id (fst <$> ops))
        >? manyP (tagSepP (snd <$> ops)) >*< inner

    withPostP ops inner =
      difoldl (taggedP (flip (,)) (\(y,i) -> (i,y)) (fst <$> ops))
        >? inner >*< manyP (tagSepP (snd <$> ops))

    -- unary operators' patterns, tagged by their positions,
    -- & tried in turn, as one partial isomorphism
    taggedP
      :: (Int -> x -> c) -- ^ tag a match
      -> (d -> (Int, y)) -- ^ untag a build
      -> [APrism x y x y] -> PartialIso x y c d
    taggedP tag untag pats =
      let (fwd, bwd) = orP (zipWith exchange [0 ..] pats) in partialIso fwd bwd
      where
        exchange i pat = let (match, build) = patternFns pat in
          (fmap (tag i) . match, \d -> case untag d of
            (j, y) | j == i -> Just (build y)
            _ -> Nothing)

    -- An operand, then @(operator, operand)@ steps, folded by each
    -- operator's associativity, like parsec's @buildExpressionParser@:
    -- https://hackage.haskell.org/package/parsec/docs/src/Text.Parsec.Expr.html
    infixP infixes term =
      prism (uncurry go) (Right . fwd) >? term >*< manyP (tagSepP syms >*< term)
      where
        syms = [sym | (_,_,sym) <- infixes]
        fns = [(associativity,f,g) | (associativity,pat,_) <- infixes, let (f,g) = patternFns pat]

        assocOf i = let (associativity,_,_) = fns !! i in associativity
        applyTag i (l,r) = let (_,_,g) = fns !! i in g (l,r)

        -- fold a shared seed together with a left-to-right list of tagged
        -- steps, dispatching on each step's `Assoc`iativity in turn
        go l [] = l
        go l ((i,r):more) = case assocOf i of
          RightAssoc -> applyTag i (l, go r more)
          _          -> go (applyTag i (l,r)) more

        -- the exact inverse of `go`: decompose a value into a seed and the
        -- list of tagged steps that `go` would fold back into that value
        fwd x = decompose x
          where
            decompose y = case tryTags y of
              Nothing -> (y, [])
              Just (i,l,r) -> case assocOf i of
                RightAssoc ->
                  let (r0, rest) = decompose r in (l, (i,r0) : rest)
                _ ->
                  let (l0, prior) = decompose l in (l0, prior ++ [(i,r)])
            tryTags y = orP
              [ (\(l,r) -> (i,l,r)) <$> f y
              | (i,(_,f,_)) <- zip [0 :: Int ..] fns ]

    -- an operator's constructor pattern, matching partially & building totally
    patternFns pat = withPrism pat $ \construct match ->
      (either (const Nothing) Just . match, construct)
