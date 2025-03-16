{- |
Module      : Control.Lens.PartialIso
Description : partial isomorphisms
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable

See Rendel & Ostermann,
[Invertible syntax descriptions](https://www.informatik.uni-marburg.de/~rendel/unparse/)
-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Control.Lens.PartialIso
  ( -- * PartialIso
    dimapMaybe
  , PartialIso
  , PartialIso'
  , APartialIso
  , PartialExchange (PartialExchange)
    -- Combinators
  , partialIso
  , withPartialIso
  , clonePartialIso
  , coPartialIso
  , crossPartialIso
  , altPartialIso
    -- * Actions
  , (>?)
  , (?<)
  , (>?<)
  , mapIso
  , coPrism
    -- * Patterns
  , satisfied
  , nulled
  , notNulled
  , streamed
  , maybeEot
  , listEot
    -- * Iterations
  , iterating
  , difoldl1
  , difoldr1
  , difoldl
  , difoldr
  , difoldl'
  , difoldr'
  ) where

import Control.Lens
import Control.Lens.Internal.Profunctor
import Control.Monad
import Data.Functor.Compose
import Data.Profunctor
import Data.Profunctor.Monad
import Data.Profunctor.Yoneda
import Witherable

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
by combining `Control.Lens.Prism.Prism`s and coPrisms.

Every `Control.Lens.Iso.Iso` & `Control.Lens.Prism.Prism` is `APartialIso`.

`PartialIso`s are isomorphic to `PartialExchange`s.
-}
type PartialIso s t a b = forall p f.
  (Choice p, Cochoice p, Applicative f, Filterable f)
    => p a (f b) -> p s (f t)

{- |
A simple `PartialIso'` @s a@ is an identification of
a subset of @s@ with a subset of @a@.

Given a simple `PartialIso'`, @partialIso f g@, has properties:

prop> Just = f <=< g
prop> Just = g <=< f

These are left and right inverse laws for proper `PartialIso'`s.
However, sometimes an improper `PartialIso'` will be useful.
For an improper `PartialIso'`, only the left inverse law holds.

prop> Just = f <=< g

For an improper `PartialIso'`, @norm = g <=< f@ is an idempotent

prop> norm = norm <=< norm

and can be regarded as a normalization within
some equivalence class of terms.
-}
type PartialIso' s a = PartialIso s s a a

{- | If you see `APartialIso` in a signature for a function,
the function is expecting a `PartialIso`. -}
type APartialIso s t a b =
  PartialExchange a b a (Maybe b) -> PartialExchange a b s (Maybe t)

{- | A `PartialExchange` provides efficient access
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

{- | Build a `PartialIso`. -}
partialIso :: (s -> Maybe a) -> (b -> Maybe t) -> PartialIso s t a b
partialIso f g =
  unright . iso (maybe (Left ()) Right . f =<<) (mapMaybe g) . right'

{- | Convert `APartialIso` to the pair of functions that characterize it. -}
withPartialIso
  :: APartialIso s t a b
  -> ((s -> Maybe a) -> (b -> Maybe t) -> r)
  -> r
withPartialIso i k =
  case i (PartialExchange Just (Just . Just)) of
    PartialExchange f g -> k f (join . g)

{- | Clone `APartialIso` so that you can reuse the same
monomorphically typed partial isomorphism for different purposes.
-}
clonePartialIso
  :: APartialIso s t a b
  -> PartialIso s t a b
clonePartialIso i = withPartialIso i $ \f g -> partialIso f g

{- | Clone and invert `APartialIso`. -}
coPartialIso
  :: APartialIso b a t s
  -> PartialIso s t a b
coPartialIso i =
  withPartialIso i $ \f g -> partialIso g f

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

{- | Action of a coPrism on `Cochoice` `Profunctor`s. -}
(?<)
  :: Cochoice p
  => APrism b a t s
  -> p a b
  -> p s t
(?<) pat = withPrism pat $ \f g -> unright . dimap (either id f) g
infixl 4 ?<

{- | Action of `APartialIso` on `Choice` and `Cochoice` `Profunctor`s. -}
(>?<)
  :: (Choice p, Cochoice p)
  => APartialIso s t a b
  -> p a b
  -> p s t
(>?<) pat = withPartialIso pat dimapMaybe
infixl 4 >?<

{- | Action of `AnIso` on `Profunctor`s. -}
mapIso :: Profunctor p => AnIso s t a b -> p a b -> p s t
mapIso i = withIso i dimap

{- | Action of a `coPrism`
on the composition of a `Profunctor` and `Filterable`.
-}
coPrism :: (Profunctor p, Filterable f) => APrism b a t s -> p a (f b) -> p s (f t)
coPrism p = unwrapPafb . (?<) p . WrapPafb

{- | `satisfied` is the prototypical proper partial isomorphism,
identifying a subset which satisfies a predicate. -}
satisfied :: (a -> Bool) -> PartialIso' a a
satisfied f = partialIso satiate satiate where
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

{- | `streamed` is an isomorphism between
two stream types with the same token type. -}
streamed
  :: (AsEmpty s, AsEmpty t, Cons s s c c, Cons t t c c)
  => Iso' s t
streamed = iso convertStream convertStream
  where
    convertStream s =
      maybe
        Empty
        (\(h,t) -> cons h (convertStream t))
        (uncons s)

{- | The either-of-tuples representation of `Maybe`. -}
maybeEot :: Iso (Maybe a) (Maybe b) (Either () a) (Either () b)
maybeEot = iso
  (maybe (Left ()) Right)
  (either (pure Nothing) Just)

{- | The either-of-tuples representation of list-like streams. -}
listEot
  :: (Cons s s a a, AsEmpty t, Cons t t b b)
  => Iso s t (Either () (a,s)) (Either () (b,t))
listEot = iso
  (maybe (Left ()) Right . uncons)
  (either (const Empty) (review _Cons))

{- | Iterate the application of a partial isomorphism,
useful for constructing fold/unfold isomorphisms. -}
iterating :: APartialIso a b a b -> Iso a b a b
iterating i = withPartialIso i $ \f g ->
  iso (iter f) (iter g) where
    iter h state = maybe state (iter h) (h state)

{- | Left fold & unfold `APartialIso` to an `Control.Lens.Iso.Iso`. -}
difoldl1
  :: Cons s t a b
  => APartialIso (c,a) (d,b) c d
  -> Iso (c,s) (d,t) (c,s) (d,t)
difoldl1 i =
  let
    associate = iso
      (\(c,(a,s)) -> ((c,a),s))
      (\((d,b),t) -> (d,(b,t)))
    step
      = crossPartialIso id _Cons
      . associate
      . crossPartialIso i id
  in iterating step

{- | Right fold & unfold `APartialIso` to an `Control.Lens.Iso.Iso`. -}
difoldr1
  :: Cons s t a b
  => APartialIso (a,c) (b,d) c d
  -> Iso (s,c) (t,d) (s,c) (t,d)
difoldr1 i =
  let
    reorder = iso
      (\((a,s),c) -> (s,(a,c)))
      (\(t,(b,d)) -> ((b,t),d))
    step
      = crossPartialIso _Cons id
      . reorder
      . crossPartialIso id i
  in iterating step

{- | Left fold & unfold `APartialIso` to a `PartialIso`. -}
difoldl
  :: (AsEmpty s, AsEmpty t, Cons s t a b)
  => APartialIso (c,a) (d,b) c d
  -> PartialIso (c,s) (d,t) c d
difoldl i =
  let
    unit' = iso
      (\(a,()) -> a)
      (\a -> (a,()))
  in
    difoldl1 i
    . crossPartialIso id nulled
    . unit'

{- | Right fold & unfold `APartialIso` to a `PartialIso`. -}
difoldr
  :: (AsEmpty s, AsEmpty t, Cons s t a b)
  => APartialIso (a,c) (b,d) c d
  -> PartialIso (s,c) (t,d) c d
difoldr i =
  let
    unit' = iso
      (\((),c) -> c)
      (\d -> ((),d))
  in
    difoldr1 i
    . crossPartialIso nulled id
    . unit'

{- | Left fold & unfold `Control.Lens.Prism.APrism'`
to a `Control.Lens.Prism.Prism'`. -}
difoldl'
  :: (AsEmpty s, Cons s s a a)
  => APrism' (c,a) c
  -> Prism' (c,s) c
difoldl' i =
  let
    unit' = iso
      (\(a,()) -> a)
      (\a -> (a,()))
  in
    difoldl1 (clonePrism i)
    . aside _Empty
    . unit'

{- | Right fold & unfold `Control.Lens.Prism.APrism'`
to a `Control.Lens.Prism.Prism'`. -}
difoldr'
  :: (AsEmpty s, Cons s s a a)
  => APrism' (a,c) c
  -> Prism' (s,c) c
difoldr' i =
  let
    unit' = iso
      (\((),c) -> c)
      (\c -> ((),c))
    asideFst k =
      withPrism k $ \bt seta ->
        prism (first' bt) $ \(s,e) ->
          case seta s of
            Left t -> Left  (t,e)
            Right a -> Right (a,e)
  in
    difoldr1 (clonePrism i)
    . asideFst _Empty
    . unit'

-- Orphanage --

instance (Profunctor p, Functor f)
  => Functor (WrappedPafb f p a) where fmap = rmap
deriving via Compose (p a) f instance
  (Profunctor p, Functor (p a), Filterable f)
    => Filterable (WrappedPafb f p a)
instance (Profunctor p, Filterable f)
  => Cochoice (WrappedPafb f p) where
    unleft (WrapPafb p) = WrapPafb $
      dimap Left (mapMaybe (either Just (const Nothing))) p
    unright (WrapPafb p) = WrapPafb $
      dimap Right (mapMaybe (either (const Nothing) Just)) p
instance (Profunctor p, Filterable (p a))
  => Filterable (Yoneda p a) where
    catMaybes = proreturn . catMaybes . proextract
instance (Profunctor p, Filterable (p a))
  => Filterable (Coyoneda p a) where
    catMaybes = proreturn . catMaybes . proextract
instance Filterable (Forget r a) where
  catMaybes (Forget f) = Forget f
instance Filterable f => Filterable (Star f a) where
  catMaybes (Star f) = Star (catMaybes . f)
