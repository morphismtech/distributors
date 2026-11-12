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
  , PartialExchange (PartialExchange)
    -- * Combinators
  , partialIso
  , partialInvoluted
  , withPartialIso
  , clonePartialIso
  , coPartialIso
  , crossPartialIso
  , altPartialIso
    -- * Applicators
  , dimapMaybe
  , (>?)
  , (?<)
  , (>?<)
  , (>~)
  , (~<)
  , (!=)
  , filterPrism
    -- * Patterns
  , satisfied
  , nulled
  , notNulled
  , eotMaybe
  , eotList
    -- * Iterators
  , iterating
  , difoldl1
  , difoldr1
  , difoldl
  , difoldr
    -- * Template Haskell
  , makeNestedPrisms
    -- * Re-exports
  , module Control.Lens.Iso
  , module Control.Lens.Prism
  ) where

import Control.Lens
import Control.Lens.Internal.Distributor.Orphanage ()
import Control.Lens.Internal.Distributor.NestedPrismTH
import Control.Lens.Internal.Profunctor
import Control.Lens.Iso
import Control.Lens.Prism
import Control.Monad
import Data.Monoid.Disjunctive
import Data.Profunctor
import Witherable

-- $setup
-- >>> import Control.Lens

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

Writing ⊂ for "every one is a",

`Control.Lens.Iso.Iso` ∪ `Control.Lens.Prism.Prism` ∪ `filterPrism`
⊂ `PartialIso` ⊂ `Control.Lens.Bifocal.Bifocal`.

__N.B.__ t'PartialExchange' is a retract of `PartialIso`:
`withPartialIso` is a retraction, with `partialIso` its section,
recovering the partial functions which build a `PartialIso`.

> prop> withPartialIso (partialIso f g) PartialExchange = PartialExchange f g

But they aren't isomorphic, since a `PartialIso` may be more than
its partial functions, as a `Control.Lens.Prism.Prism` is, below.
Rebuilding a `PartialIso` from its partial functions,
by `clonePartialIso`, is idempotent, but not the identity.

> prop> clonePartialIso pattern = withPartialIso pattern partialIso
> prop> clonePartialIso (clonePartialIso pattern) = clonePartialIso pattern

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
passing a mismatched source through, where its partial functions,
cloned by `clonePartialIso`, fail; so it isn't its own clone.

>>> traverseOf _Just (Just . succ) Nothing
Just Nothing
>>> traverseOf (clonePartialIso _Just) (Just . succ) Nothing
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

Given a simple `PartialIso'`, @partialIso f g@, has properties:

> prop> Just = f <=< g
> prop> Just = g <=< f

These are left and right inverse laws for proper `PartialIso'`s.
However, sometimes an improper `PartialIso'` will be useful.
For an improper `PartialIso'`, only the left inverse law holds.

> prop> Just = f <=< g

For an improper `PartialIso'`, @norm = g <=< f@ is an idempotent

> prop> norm = norm <=< norm

and can be regarded as a normalization within
some equivalence class of terms.
-}
type PartialIso' s a = PartialIso s s a a

{- | `APartialIso` is monomorphically a `PartialIso`. -}
type APartialIso s t a b =
  PartialExchange a b a (Maybe b) -> PartialExchange a b s (Maybe t)

{- | A t'PartialExchange' provides efficient access
to the two functions that make up a `PartialIso`.
-}
data PartialExchange a b s t =
  PartialExchange (s -> Maybe a) (b -> Maybe t)
instance Functor (PartialExchange a b s) where fmap = rmap
instance Filterable (PartialExchange a b s) where
  mapMaybe = dimapMaybe Just
instance Profunctor (PartialExchange a b) where
  dimap f' g' (PartialExchange f g) =
    PartialExchange (f . f') (fmap g' . g)
instance Choice (PartialExchange a b) where
  left' (PartialExchange f g) =
    PartialExchange (either f (pure Nothing)) ((Left <$>) . g)
  right' (PartialExchange f g) =
    PartialExchange (either (pure Nothing) f) ((Right <$>) . g)
instance Cochoice (PartialExchange a b) where
  unleft (PartialExchange f g) =
    PartialExchange (f . Left) (either Just (pure Nothing) <=< g)
  unright (PartialExchange f g) =
    PartialExchange (f . Right) (either (pure Nothing) Just <=< g)
{- | t'PartialExchange's choose by first success, in either direction,
& `falseP` fails in both, so `Data.Monoid.Disjunctive.orP` tries
the partial functions of `PartialIso`s in turn.

`satisfied` is a homomorphism of `Data.Monoid.Disjunctive.BooleanAlgebra`s
of predicates, from `>|<` to `>|<`, & from `>&<` to composition.

> prop> withPartialIso (satisfied (p >|< q)) PartialExchange = withPartialIso (satisfied p) PartialExchange >|< withPartialIso (satisfied q) PartialExchange
> prop> withPartialIso (satisfied falseP) PartialExchange = falseP
> prop> satisfied (p >&< q) = satisfied p . satisfied q
> prop> satisfied trueP = id
-}
instance DisjunctiveMonoid (PartialExchange a b s t) where
  falseP = PartialExchange falseP falseP
  PartialExchange f g >|< PartialExchange f' g' =
    PartialExchange (f >|< f') (g >|< g')

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

{- | Convert `APartialIso` to the pair of functions that characterize it. -}
withPartialIso
  :: APartialIso s t a b
  -> ((s -> Maybe a) -> (b -> Maybe t) -> r)
  -> r
withPartialIso pattern k =
  case pattern (PartialExchange Just (Just . Just)) of
    PartialExchange f g -> k f (join . g)

{- | Clone `APartialIso` so that you can reuse the same
monomorphically typed partial isomorphism for different purposes.
-}
clonePartialIso
  :: APartialIso s t a b
  -> PartialIso s t a b
clonePartialIso pattern = withPartialIso pattern $ \f g -> partialIso f g

{- | Clone and invert `APartialIso`. -}
coPartialIso
  :: APartialIso b a t s
  -> PartialIso s t a b
coPartialIso pattern =
  withPartialIso pattern $ \f g -> partialIso g f

{- | Construct a `PartialIso` on pairs from components. -}
crossPartialIso
  :: APartialIso s t a b
  -> APartialIso u v c d
  -> PartialIso (s,u) (t,v) (a,c) (b,d)
crossPartialIso x y =
  withPartialIso x $ \e f ->
  withPartialIso y $ \g h ->
    partialIso
      (\(s,u) -> (,) <$> e s <*> g u)
      (\(t,v) -> (,) <$> f t <*> h v)

{- | Construct a `PartialIso` on `Either`s from components. -}
altPartialIso
  :: APartialIso s t a b
  -> APartialIso u v c d
  -> PartialIso
      (Either s u) (Either t v)
      (Either a c) (Either b d)
altPartialIso x y =
  withPartialIso x $ \e f ->
  withPartialIso y $ \g h ->
    partialIso
      (either ((Left <$>) . e) ((Right <$>) . g))
      (either ((Left <$>) . f) ((Right <$>) . h))

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

{- | Action of `APartialIso` on `Choice` & `Cochoice` partial profunctors. -}
(>?<)
  :: (Choice p, Cochoice p)
  => APartialIso s t a b
  -> p a b
  -> p s t
(>?<) pat = withPartialIso pat dimapMaybe
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
identifying a subset which satisfies a predicate. -}
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
      = crossPartialIso id _Cons
      . associate
      . crossPartialIso (coPartialIso pattern) id
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
      = crossPartialIso _Snoc id
      . reorder
      . crossPartialIso id (coPartialIso pattern)
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
