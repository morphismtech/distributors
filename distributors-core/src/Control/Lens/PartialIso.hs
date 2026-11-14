{- |
Module      : Control.Lens.PartialIso
Description : partial isomorphisms
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable

See Rendel & Ostermann,
[Invertible syntax descriptions](https://www.informatik.uni-marburg.de/~rendel/unparse/)
-}

module Control.Lens.PartialIso
  ( -- * PartialIso
    PartialIso
  , PartialIso'
  , APartialIso
  , PartialMarket (..), partialMarket, withPartialMarket
    -- * Combinators
  , partialIso
  , partialInvoluted
  , withPartialIso
  , clonePartialIso
  , coPartialIso
  , alongsidePartialIso
  , withoutPartialIso
  , orPartialIso
  , falsePartialIso
    -- * Applicators
  , dimapMaybe
  , (>?)
  , (?<)
  , (>?<)
  , (>~)
  , (~<)
  , (!=)
    -- * Patterns
  , filterPrism
  , satisfied
  , nulled
  , notNulled
  , eotMaybe
  , eotList
  , listed
    -- * Iterators
  , iterating
  , difoldl1
  , difoldr1
  , difoldl
  , difoldr
    -- * Nested prisms
  , makeNestedPrisms
  , genericNestedPrism
  , genericNestedIso
    -- * Re-exports
  , module Control.Lens.Iso
  , module Control.Lens.Prism
  ) where

import Control.Lens
import Control.Lens.Internal.Distributor.Orphanage ()
import Control.Lens.Prism.Nested
import Control.Lens.Internal.Profunctor
import Control.Lens.Iso
import Control.Lens.Prism
import Control.Applicative
import Control.Monad
import Data.Monoid.Disjunctive
import Data.Profunctor
import Witherable
import GHC.IsList (IsList (..))

-- $setup
-- >>> import Control.Lens
-- >>> import Data.Monoid.Disjunctive ((>|<))
-- >>> import Data.Sequence (Seq)
-- >>> import GHC.IsList (fromList)

{- | The `dimapMaybe` function endows
`Choice` & `Cochoice` "partial profunctors"
with an action `>?<` of `PartialIso`s.
-}
dimapMaybe
  :: (Choice p, Cochoice p)
  => (s -> Maybe a) -> (b -> Maybe t)
  -> p a b -> p s t
dimapMaybe f g =
  let
    m2e h = maybe (Left ()) Right . h
    fg = dimap (>>= m2e f) (>>= m2e g)
  in
    unright . fg . right'

{- | `PartialIso` is a first class inexhaustive pattern,
similar to how `Control.Lens.Prism.Prism` is a first class exhaustive pattern,
by combining `Control.Lens.Prism.Prism`s, constructor patterns,
with `filterPrism`s, filter patterns.

`Control.Lens.Iso.Iso` ∪ `Control.Lens.Prism.Prism` ∪ `filterPrism`
⊂ `PartialIso` ⊂ `Control.Lens.Bifocal.Bifocal`.

Applied to a value, a pattern does one of three things.
It __matches__, focusing on part of the value, to work on & rebuild.
Or it doesn't match, & either __passes the value through__, untouched,
as a `Control.Lens.Prism.Prism` does, so there is nothing to work on,
but nothing goes wrong; or it __fails__, rejecting the value,
as a filter does. A `PartialIso` may do any of the three.

>>> traverseOf _Just (Just . succ) (Just 1)
Just (Just 2)
>>> traverseOf _Just (Just . succ) Nothing
Just Nothing
>>> traverseOf (satisfied even) (Just . succ) 3
Nothing

Here `_Just` matches @Just 1@, & passes @Nothing@ through,
while @`satisfied` `even`@ fails on @3@.
Passing through & failing can only be told apart where a result
can succeed with nothing done, like `traverseOf`'s; a parser can't,
since a value that doesn't match isn't parsed, so it fails.

`PartialIso`s are the compositions of `Control.Lens.Prism.Prism`s,
which pass a mismatch through, & `filterPrism`s, which fail,
forwards where they reject what a `Control.Lens.Prism.Prism` passes through.
Each is a `filterPrism` after a `Control.Lens.Prism.Prism`,

> prop> partialMarket build match = filterPrism _Just . prism build (maybe (Left Nothing) match)

& isomorphic to a t'PartialMarket', so `clonePartialIso` is the identity.

> prop> clonePartialIso pattern = pattern

Its partial functions, by `withPartialIso`, forget passing through,
which @`withPartialIso` pattern `partialIso`@ rebuilds from, failing instead.

A `PartialIso` chooses whether its pattern matches by `Choice`,
& fails in either direction by `Filterable`,
emptying with @`catMaybes` (`pure` `Nothing`)@ & filtering with `mapMaybe`.
So it needs no `Cochoice` of its own, unlike its action `>?<`
on a `Choice` & `Cochoice` partial profunctor,
which has no `Filterable` to fail by.

>>> :{
let halve :: PartialIso' Int Int
    halve = partialIso
      (\n -> if even n then Just (n `div` 2) else Nothing)
      (Just . (* 2))
:}

Forwards, a `PartialIso` folds at most one focus,
so `preview`, `^?`, `has` & `toListOf` match by it.

>>> preview halve 6
Just 3
>>> 7 ^? halve
Nothing
>>> has halve 7
False
>>> toListOf halve 6
[3]

Backwards, a `PartialIso` folds forwards by `coPartialIso`.

>>> preview (coPartialIso halve) 3
Just 6

`withPartialIso` converts a `PartialIso` to both directions.

>>> withPartialIso halve $ \match build -> (match 6, build 3)
(Just 3,Just 6)

Since it may fail to build, as well as to match, a `PartialIso`
modifies by `traverseOf` with a `Filterable` `Applicative` like `Maybe`,
in place of `over` & `set`.

>>> traverseOf halve (Just . succ) 6
Just 8
>>> traverseOf halve (Just . succ) 7
Nothing

A `Control.Lens.Prism.Prism` is exhaustive though,
passing a mismatched source through, as does its clone,
where its partial functions, rebuilt by `partialIso`, fail.

>>> traverseOf _Just (Just . succ) Nothing
Just Nothing
>>> traverseOf (clonePartialIso _Just) (Just . succ) Nothing
Just Nothing
>>> traverseOf (withPartialIso _Just partialIso) (Just . succ) Nothing
Nothing

Neither `review`, `over` nor `set` applies to a `PartialIso`,
since t'Data.Functor.Identity.Identity' can't fail, so isn't `Filterable`;
& `view` applies only to a `Monoid`al focus, as for a
`Control.Lens.Fold.Fold`, by t'Data.Functor.Const.Const'.

`PartialIso`s compose by `.`, with each other,
& with `Control.Lens.Iso.Iso`s, `Control.Lens.Prism.Prism`s & `filterPrism`s.

>>> preview (halve . halve) 12
Just 3
>>> preview (_Just . halve) (Just 4)
Just 2
>>> preview (halve . filterPrism _Just) 6
Just (Just 3)
-}
type PartialIso s t a b = forall p f.
  (Choice p, Applicative f, Filterable f)
    => p a (f b) -> p s (f t)

{- |
A simple `PartialIso'` @s a@ is an identification of
a subset of @s@ with a subset of @a@.

A proper `PartialIso'`, with partial functions @match@ & @build@,
by `withPartialIso`, inverts what it matches & what it builds.

> prop> match s = Just a  ==>  build a = Just s
> prop> build a = Just s  ==>  match s = Just a

However, sometimes an improper `PartialIso'` will be useful,
matching what it builds, but not necessarily rebuilding what it matches.

> prop> build a = Just s  ==>  match s = Just a

For an improper `PartialIso'`, @norm = build <=< match@ is an idempotent

> prop> norm = norm <=< norm

and can be regarded as a normalization within
some equivalence class of terms.
-}
type PartialIso' s a = PartialIso s s a a

{- | `APartialIso` is monomorphically a `PartialIso`.

> prop> PartialIso s t a b ⊂ APartialIso s t a b
-}
type APartialIso s t a b =
  PartialMarket a b a (Maybe b) -> PartialMarket a b s (Maybe t)

{- | A t'PartialMarket' is the concrete form of a `PartialIso`,
isomorphic to it, a `Control.Lens.Internal.Prism.Market` which may fail
in either direction: building backwards, partially;
& matching forwards, either its focus,
or, where its pattern doesn't match, `Nothing`, failing,
or `Just` a target, passing through, as a `Control.Lens.Prism.Prism` does.

> prop> withPartialMarket (partialMarket build match) k = k build match
> prop> withPartialMarket pattern partialMarket = pattern

Its functions are those of a `Control.Lens.Prism.Prism` with a @Maybe t@
target, a `PartialIso` failing in its target, rather than in its `Filterable`,
& the conversions are inverse.

> prop> withPrism (withPartialMarket pattern prism :: Prism s (Maybe t) a b) partialMarket = (clonePartialIso pattern :: PartialIso s t a b)
> prop> withPartialMarket (withPrism prsm partialMarket :: PartialIso s t a b) prism = (clonePrism prsm :: Prism s (Maybe t) a b)

So lens's `over` & `set` apply to a `PartialIso` as such a `Control.Lens.Prism.Prism`.

>>> over (withPartialMarket (satisfied even) prism :: Prism Int (Maybe Int) Int Int) (* 2) 4
Just 8
>>> over (withPartialMarket (satisfied even) prism :: Prism Int (Maybe Int) Int Int) (* 2) 3
Nothing
>>> over (withPartialMarket _Just prism :: Prism (Maybe Int) (Maybe (Maybe Int)) Int Int) succ Nothing
Just Nothing

Only a `Choice` which isn't
`Data.Profunctor.Monoidal.Cocartesian.CocartesianChoice`
can tell passing through from failing,
like @(->)@, by `Control.Lens.Traversal.traverseOf`.

>>> withPartialMarket _Left $ \_ match -> (match (Left 'x'), match (Right 'y') :: Either (Maybe (Either Char Char)) Char)
(Right 'x',Left (Just (Right 'y')))
-}
data PartialMarket a b s t =
  PartialMarket (b -> Maybe t) (s -> Either (Maybe t) a)
instance Functor (PartialMarket a b s) where fmap = rmap
instance Filterable (PartialMarket a b s) where
  mapMaybe h (PartialMarket build match) =
    PartialMarket (h <=< build) (either (Left . (h =<<)) Right . match)
instance Profunctor (PartialMarket a b) where
  dimap f g (PartialMarket build match) =
    PartialMarket (fmap g . build) (either (Left . fmap g) Right . match . f)
instance Choice (PartialMarket a b) where
  left' (PartialMarket build match) = PartialMarket
    (fmap Left . build)
    (either (either (Left . fmap Left) Right . match) (Left . Just . Right))
  right' (PartialMarket build match) = PartialMarket
    (fmap Right . build)
    (either (Left . Just . Left) (either (Left . fmap Right) Right . match))
instance Cochoice (PartialMarket a b) where
  unleft = lmap Left . mapMaybe (either Just (const Nothing))
  unright = lmap Right . mapMaybe (either (const Nothing) Just)
{- | t'PartialMarket's choose by first success, in either direction,
& forwards, on a mismatch of both, pass through the first target passed through,
& `falseP` fails in both directions.
-}
instance DisjunctiveMonoid (PartialMarket a b s t) where
  falseP = PartialMarket (const Nothing) (const (Left Nothing))
  PartialMarket build0 match0 >|< PartialMarket build1 match1 = PartialMarket
    (\b -> build0 b <|> build1 b)
    (\s -> case match0 s of
      Right a -> Right a
      Left t0 -> case match1 s of
        Right a -> Right a
        Left t1 -> Left (t0 <|> t1))

{- | Build a `PartialIso` from the functions of a t'PartialMarket',
building backwards, partially, & matching forwards, like `prism`,
either its focus, or on a mismatch, `Just` a target to pass through,
or `Nothing` to fail.

`partialIso` builds a `PartialIso` from partial functions,
whose mismatches always fail; it is `partialMarket`
without passing through,

> prop> partialIso match build = partialMarket build (maybe (Left Nothing) Right . match)

so every `PartialIso` is a `partialMarket`, but not every one a `partialIso`,
like a `Control.Lens.Prism.Prism`, which passes a mismatch through.
They differ only at a `Choice` which can tell passing through from failing,
like @(->)@, by `traverseOf`.

>>> traverseOf (partialMarket (Just . Just) (maybe (Left (Just Nothing)) Right)) (Just . succ) (Nothing :: Maybe Int)
Just Nothing
>>> traverseOf (partialIso id (Just . Just)) (Just . succ) (Nothing :: Maybe Int)
Nothing
-}
partialMarket
  :: (b -> Maybe t) -> (s -> Either (Maybe t) a)
  -> PartialIso s t a b
partialMarket build match =
  dimap
    (either (Left . maybe (catMaybes (pure Nothing)) pure) Right . match)
    (either id (mapMaybe build))
  . right'

{- | Convert `APartialIso` to the pair of functions that characterize it,
of its t'PartialMarket', building backwards,
& matching forwards, passing through or failing, like `withPrism`. -}
withPartialMarket
  :: APartialIso s t a b
  -> ((b -> Maybe t) -> (s -> Either (Maybe t) a) -> r)
  -> r
withPartialMarket pattern k =
  case catMaybes (pattern (PartialMarket (Just . Just) Right)) of
    PartialMarket build match -> k build match

{- | Build a `PartialIso` from its partial functions,
matching forwards & building backwards,
as the action `dimapMaybe` on @p a (f b)@,
like `filterPrism` is the action `?<`.
-}
partialIso :: (s -> Maybe a) -> (b -> Maybe t) -> PartialIso s t a b
partialIso f g = unwrapPafb . dimapMaybe f g . WrapPafb

{- | Given a partial function that is its own inverse,
this gives you a `PartialIso'` using it in both directions. -}
partialInvoluted :: (a -> Maybe a) -> PartialIso' a a
partialInvoluted f = partialIso f f

{- | Convert `APartialIso` to its partial functions,
matching forwards & building backwards, like `withIso`.
They forget passing through, failing on a mismatch which a
`Control.Lens.Prism.Prism` passes through, so they characterize
only a `PartialIso` which never passes through, one built by `partialIso`;
its t'PartialMarket', by `withPartialMarket`, characterizes any.

> prop> withPartialIso (partialIso match build) k = k match build
-}
withPartialIso
  :: APartialIso s t a b
  -> ((s -> Maybe a) -> (b -> Maybe t) -> r)
  -> r
withPartialIso pattern k = withPartialMarket pattern $ \build match ->
  k (either (const Nothing) Just . match) build

{- | Clone `APartialIso` so that you can reuse the same
monomorphically typed partial isomorphism for different purposes.
It keeps a `Control.Lens.Prism.Prism`'s passing a mismatch through,
unlike rebuilding it from its partial functions,
by @`withPartialIso` pattern `partialIso`@, which fails on a mismatch instead.
They agree at every `Data.Profunctor.Monoidal.Cocartesian.CocartesianChoice`,
like a parser's, which can't tell passing through from failing,
& differ at a `Choice` which can, like @(->)@, by `traverseOf`.

> prop> clonePartialIso pattern = pattern

>>> traverseOf (clonePartialIso _Just) (Just . succ) Nothing
Just Nothing
>>> traverseOf (withPartialIso _Just partialIso) (Just . succ) Nothing
Nothing
-}
clonePartialIso
  :: APartialIso s t a b
  -> PartialIso s t a b
clonePartialIso pattern =
  withPartialMarket pattern partialMarket

{- | Clone and invert `APartialIso`, by its partial functions.
Only matching forwards can pass a value through, building backwards can't,
so the inverse of a `PartialIso` which passes through fails instead.
`coPartialIso` is its own inverse on `PartialIso`s which never pass through,
those rebuilt from their partial functions,
& inverts any other as that rebuilding.

> prop> coPartialIso pattern = coPartialIso (withPartialIso pattern partialIso)
> prop> coPartialIso (coPartialIso pattern) = withPartialIso pattern partialIso
-}
coPartialIso
  :: APartialIso b a t s
  -> PartialIso s t a b
coPartialIso pattern =
  withPartialIso pattern $ \f g -> partialIso g f

{- | Construct a `PartialIso` on pairs from components,
pairing their foci, as `Control.Lens.Lens.alongside` does,
passing a pair through where both components pass through,
& otherwise failing on a mismatch, since a pair passed through
needs a target from each component.

>>> traverseOf (alongsidePartialIso _Just _Just) (\(x, y) -> Just (x + y, x * y)) (Just 2, Just 3 :: Maybe Int)
Just (Just 5,Just 6)
>>> traverseOf (alongsidePartialIso _Just _Just) (Just . id) (Nothing, Nothing :: Maybe Int)
Just (Nothing,Nothing)
>>> traverseOf (alongsidePartialIso _Just _Just) (Just . id) (Just 2, Nothing :: Maybe Int)
Nothing
-}
alongsidePartialIso
  :: APartialIso s t a b
  -> APartialIso u v c d
  -> PartialIso (s,u) (t,v) (a,c) (b,d)
alongsidePartialIso x y =
  withPartialMarket x $ \build0 match0 ->
  withPartialMarket y $ \build1 match1 ->
    partialMarket
      (\(b,d) -> (,) <$> build0 b <*> build1 d)
      (\(s,u) -> case (match0 s, match1 u) of
        (Right a, Right c) -> Right (a,c)
        (Left t, Left v) -> Left ((,) <$> t <*> v)
        _ -> Left Nothing)

{- | Construct a `PartialIso` on `Either`s from components,
summing their foci, as `Control.Lens.Prism.without` does,
passing a mismatch through from either.

>>> traverseOf (withoutPartialIso _Just _Just) (Just . either (Left . succ) (Right . pred)) (Left (Just 1) :: Either (Maybe Int) (Maybe Int))
Just (Left (Just 2))
>>> traverseOf (withoutPartialIso _Just _Just) (Just . either (Left . succ) (Right . pred)) (Left Nothing :: Either (Maybe Int) (Maybe Int))
Just (Left Nothing)
-}
withoutPartialIso
  :: APartialIso s t a b
  -> APartialIso u v c d
  -> PartialIso
      (Either s u) (Either t v)
      (Either a c) (Either b d)
withoutPartialIso x y =
  withPartialMarket x $ \build0 match0 ->
  withPartialMarket y $ \build1 match1 ->
    partialMarket
      (either (fmap Left . build0) (fmap Right . build1))
      (either
        (either (Left . fmap Left) (Right . Left) . match0)
        (either (Left . fmap Right) (Right . Right) . match1))

{- | The union of two patterns, trying the first, then the second,
in either direction, & on a mismatch of both,
passing through the first target passed through,
by the `DisjunctiveMonoid` of their t'PartialMarket's.

>>> [traverseOf (orPartialIso (satisfied even) (satisfied odd)) Just n | n <- [2, 3 :: Int]]
[Just 2,Just 3]

__N.B.__ `>|<` on `APartialIso`s typechecks, pointwise, but is wrong:
it chooses within @PartialMarket a b s (Maybe t)@, whose @`Just` `Nothing`@
is a failure, which it takes for a success.

>>> [traverseOf (clonePartialIso (satisfied even >|< satisfied odd)) Just n | n <- [2, 3 :: Int]]
[Just 2,Nothing]
-}
orPartialIso
  :: APartialIso s t a b
  -> APartialIso s t a b
  -> PartialIso s t a b
orPartialIso x y =
  withPartialMarket x $ \build0 match0 ->
  withPartialMarket y $ \build1 match1 ->
    case PartialMarket build0 match0 >|< PartialMarket build1 match1 of
      PartialMarket build match -> partialMarket build match

{- | The pattern which never matches & never builds,
failing in both directions, the identity of `orPartialIso`.

> prop> orPartialIso falsePartialIso pattern = clonePartialIso pattern
> prop> orPartialIso pattern falsePartialIso = clonePartialIso pattern
> prop> satisfied (const False) = falsePartialIso

>>> preview falsePartialIso 'x' :: Maybe Char
Nothing
-}
falsePartialIso :: PartialIso s t a b
falsePartialIso = partialMarket (const Nothing) (const (Left Nothing))

{- | Action of `APrism` on `Choice` `Profunctor`s. -}
(>?)
  :: Choice p
  => APrism s t a b
  -> p a b
  -> p s t
(>?) pat = withPrism pat $ \f g -> dimap g (either id f) . right'
infixl 4 >?

{- | The coprism, the action of a reversed `APrism`
on `Cochoice` `Profunctor`s, feeding the residual of a mismatch
back by `unright`, as in
[profunctor-optics](https://hackage.haskell.org/package/profunctor-optics),
where @coprism f g = re (prism f g)@.
`filterPrism` acts by it on @p a (f b)@,
whose `Cochoice` by a `Filterable` @f@ filters the residual out.
-}
(?<)
  :: Cochoice p
  => APrism b a t s
  -> p a b
  -> p s t
(?<) pat = withPrism pat $ \f g -> unright . dimap (either id f) g
infixl 4 ?<

{- | Action of `APartialIso` on `Choice` & `Cochoice` partial profunctors,
passing a mismatch through by `Choice`, as `>?` does,
& failing by `Cochoice`, as `dimapMaybe` does,
so it acts on a `Control.Lens.Prism.Prism` as `>?` does,
& on partial functions as `dimapMaybe` does.

> prop> prsm >?< p = prsm >? p
> prop> partialIso match build >?< p = dimapMaybe match build p

A `Control.Lens.Prism.Prism` with a @Maybe t@ target acts,
by its `PartialIso`, as it does, filtering its target,
on a `Data.Profunctor.Filtrator.Filtrator`.

> prop> withPrism prsm partialMarket >?< p = catMaybes (prsm >? p)
-}
(>?<)
  :: (Choice p, Cochoice p)
  => APartialIso s t a b
  -> p a b
  -> p s t
(>?<) pat = withPartialMarket pat $ \build match ->
  unright . dimap
    (either (const (Left Nothing)) match)
    (either (maybe (Left ()) Right) (maybe (Left ()) Right . build))
  . right'
infixl 4 >?<

{- | Action of `AnIso` on `Profunctor`s. -}
(>~) :: Profunctor p => AnIso s t a b -> p a b -> p s t
(>~) pattern = withIso pattern dimap
infixl 2 >~

{- | Inverse action of `AnIso` on `Profunctor`s. -}
(~<) :: Profunctor p => AnIso b a t s -> p a b -> p s t
(~<) pattern = withIso pattern (flip dimap)
infixl 2 ~<

{- | An optional value,
missing exactly when it's the default,
like `Data.Aeson.!=`,
by the `non` isomorphism.

> prop> optP != def = non def ~< optP
-}
(!=)
  :: (Eq a, Profunctor q)
  => q (Maybe a) (Maybe a) -- ^ optional
  -> a -- ^ default
  -> q a a
prop != def = non def ~< prop
infix 6 !=

{- | A filter pattern of `APrism`, as the coprism `?<` acts on @p a (f b)@,
total forwards & partial backwards, failing by `Filterable` alone.
As a `Control.Lens.Prism.Prism` is a constructor pattern,
like @Right x@ in a @case@ expression, passing any other case through,
a `filterPrism` is a filter pattern,
like @Right x <- xs@ in a comprehension or a @do@ block,
filtering any other case out, by discarding the residual of a mismatch.
It runs as its `Control.Lens.Prism.Prism` does, reversed,
building forwards by `view`, as the prism `review`s,
& matching backwards by `preview` of its `coPartialIso`,
as the prism `preview`s.

>>> view (filterPrism _Just) 'x'
Just 'x'
>>> preview (coPartialIso (filterPrism _Just)) (Just 'x')
Just 'x'
>>> preview (coPartialIso (filterPrism _Just)) (Nothing :: Maybe Char)
Nothing

An optic for `Data.Profunctor.Filtrator.Filtrator`s may only map its source
& filter its target, as a `filterPrism` does, since by its laws,
a `Data.Profunctor.Filtrator.Filtrator`'s `Cochoice` derives from
its `Profunctor` & `Filterable` structure,
@unleft = lmap Left . mapMaybe (either Just (const Nothing))@.
-}
filterPrism
  :: (Profunctor p, Filterable f)
  => APrism b a t s -> p a (f b) -> p s (f t)
filterPrism p = unwrapPafb . (?<) p . WrapPafb

{- | `satisfied` is the prototypical proper partial isomorphism,
identifying a subset which satisfies a predicate.

It is a homomorphism of `Data.Monoid.Disjunctive.BooleanAlgebra`s
of predicates, from `>|<` to `>|<` of its partial functions,
which choose by first success, in either direction,
& from `>&<` to composition.

> prop> withPartialIso (satisfied (p >|< q)) (,) = withPartialIso (satisfied p) (,) >|< withPartialIso (satisfied q) (,)
> prop> withPartialIso (satisfied falseP) (,) = falseP
> prop> satisfied (p >&< q) = satisfied p . satisfied q
> prop> satisfied trueP = id
-}
satisfied :: (a -> Bool) -> PartialIso' a a
satisfied f = partialInvoluted satiate where
  satiate a = if f a then Just a else Nothing

{- | `nulled` matches an `Empty` pattern, like `_Empty`. -}
nulled :: (AsEmpty s, AsEmpty t) => PartialIso s t () ()
nulled = partialIso empA empB where
  empA s = if isn't _Empty s then Nothing else Just ()
  empB _ = Just Empty

{- | `notNulled` matches a non-`Empty` pattern. -}
notNulled :: (AsEmpty s, AsEmpty t) => PartialIso s t s t
notNulled = partialIso nonEmp nonEmp where
  nonEmp s = if isn't _Empty s then Just s else Nothing

{- | The either-of-tuples representation of `Maybe`,
in the order of its constructors.
-}
eotMaybe :: Iso (Maybe a) (Maybe b) (Either () a) (Either () b)
eotMaybe = iso
  (maybe (Left ()) Right)
  (either (const Nothing) Just)

{- | The either-of-tuples representation of list-like streams,
empty or else a cons, as lists' constructors are ordered.
-}
eotList
  :: (Cons s s a a, AsEmpty t, Cons t t b b)
  => Iso s t (Either () (a,s)) (Either () (b,t))
eotList = iso
  (maybe (Left ()) Right . uncons)
  (either (const Empty) (review _Cons))

{- | A list of items as an `IsList`, like lens's @List@ pattern.
Act on an `IsList` as on lists by @listed ~< p@;
optically, into its items by @from listed@.

>>> review listed (fromList "abc" :: Seq Char)
"abc"
-}
listed :: (IsList s, IsList t) => Iso [Item s] [Item t] s t
listed = iso fromList toList

{- | Iterate the application of a partial isomorphism,
useful for constructing fold/unfold isomorphisms. -}
iterating :: APartialIso a b a b -> Iso a b a b
iterating pattern = withPartialIso pattern $ \f g ->
  iso (iter f) (iter g) where
    iter h state = maybe state (iter h) (h state)

{- | Left fold & unfold `APartialIso` to an `Control.Lens.Iso.Iso`. -}
difoldl1
  :: Cons s t a b
  => APartialIso d c (d,b) (c,a)
  -> Iso (d,t) (c,s) (d,t) (c,s)
difoldl1 pattern =
  let
    associate = iso
      (\(c,(a,s)) -> ((c,a),s))
      (\((d,b),t) -> (d,(b,t)))
    step
      = alongsidePartialIso id _Cons
      . associate
      . alongsidePartialIso (coPartialIso pattern) id
  in from (iterating step)

{- | Right fold & unfold `APartialIso` to an `Control.Lens.Iso.Iso`. -}
difoldr1
  :: Snoc s t a b
  => APartialIso d c (b,d) (a,c)
  -> Iso (t,d) (s,c) (t,d) (s,c)
difoldr1 pattern =
  let
    reorder = iso
      (\((s,a),c) -> (s,(a,c)))
      (\(t,(b,d)) -> ((t,b),d))
    step
      = alongsidePartialIso _Snoc id
      . reorder
      . alongsidePartialIso id (coPartialIso pattern)
  in from (iterating step)

{- | Left fold & unfold `APartialIso` to a `Control.Lens.Prism.Prism`. -}
difoldl
  :: (AsEmpty t, Cons s t a b)
  => APartialIso d c (d,b) (c,a)
  -> Prism d c (d,t) (c,s)
difoldl pattern
  = dimap (,Empty) (fmap fst)
  . difoldl1 pattern

{- | Right fold & unfold `APartialIso` to a `Control.Lens.Prism.Prism`. -}
difoldr
  :: (AsEmpty t, Snoc s t a b)
  => APartialIso d c (b,d) (a,c)
  -> Prism d c (t,d) (s,c)
difoldr pattern
  = dimap (Empty,) (fmap snd)
  . difoldr1 pattern
