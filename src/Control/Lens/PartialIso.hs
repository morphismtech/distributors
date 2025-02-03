{- |
Module      : Control.Lens.PartialIso
Description : partial isomorphisms
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Control.Lens.PartialIso
  ( -- * Partial Isomorphisms
    PartialIso
  , PartialIso'
  , APartialIso
  , APartialIso'
  , PartialExchange (PartialExchange)
    -- * Constructing and Consuming Partial Isomorphisms
  , partialIso
  , withPartialIso
  , clonePartialIso
  , coPartialIso
  , crossPartialIso
  , altPartialIso
  , iterating
    -- * Prism, Coprism and (Partial)Iso Actions
  , mapPrism
  , mapCoprism
  , mapPartialIso
  , mapIso
    -- * Common (Partial)Isos
  , _Satisfy
  , _Normal
  , _M2E
    -- * difold/dichain operations
  , difoldl1
  , difoldr1
  , difoldl
  , difoldl'
  , difoldr
  , difoldr'
  , dichainl
  , dichainr
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.Token
import Control.Monad
import Data.Profunctor
import Data.Profunctor.Distributor
import Witherable

{- | A `PartialExchange` provides efficient access
to the two functions that make up a `PartialIso`.
-}
data PartialExchange a b s t =
  PartialExchange (s -> Maybe a) (b -> Maybe t)
instance Semigroup (PartialExchange a b s t) where
  PartialExchange f g <> PartialExchange f' g' =
    PartialExchange (\s -> f s <|> f' s) (\b -> g b <|> g' b)    
instance Monoid (PartialExchange a b s t) where
  mempty = PartialExchange nope nope where
    nope _ = Nothing
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
instance Tokenized a b (PartialExchange a b) where
  anyToken = PartialExchange Just Just

{- | `PartialIso` is a first class inexhaustive pattern,
similar to how `Control.Lens.Prism.Prism` is a first class exhaustive pattern.

`PartialIso` is part of a subtyping order:

prop> Iso s t a b < Prism s t a b < PartialIso s t a b

`PartialIso`s are a functionalization of `PartialExchange`s.

>>> :{
let
  fromPartialIso :: APartialIso s t a b -> PartialExchange a b s t
  fromPartialIso i = withPartialIso i PartialExchange
  toPartialIso :: PartialExchange a b s t -> PartialIso s t a b
  toPartialIso (PartialExchange f g) = partialIso f g
:}
prop> id = fromPartialIso . toPartialIso
prop> id = toPartialIso . fromPartialIso
-}
type PartialIso s t a b = forall p f.
  (Choice p, Cochoice p, Applicative f, Filterable f)
    => p a (f b) -> p s (f t)

{- |
A `PartialIso'` @s a@ is a `Simple` `PartialIso`.
It is an identification of a subset of @s@ with a subset of @a@.

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

{- | If you see this in a signature for a function,
the function is expecting a `PartialIso`. -}
type APartialIso s t a b =
  PartialExchange a b a (Maybe b) -> PartialExchange a b s (Maybe t)

{- | `Simple` `APartialIso` -}
type APartialIso' s a = APartialIso s s a a

{- | Build a `PartialIso`. -}
partialIso :: (s -> Maybe a) -> (b -> Maybe t) -> PartialIso s t a b
partialIso f g =
  unright . iso (view _M2E . f =<<) (mapMaybe g) . right'

{- | `withPartialIso` inverts `partialIso`. -}
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

{- | Iterate the application of a partial isomorphism,
useful for constructing fold/unfold isomorphisms. -}
iterating :: APartialIso a b a b -> Iso a b a b
iterating i = withPartialIso i $ \f g ->
  iso (iter f) (iter g) where
    iter h state = maybe state (iter h) (h state)

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
mapPrism
  :: Choice p
  => APrism s t a b
  -> p a b
  -> p s t
mapPrism pat = withPrism pat $ \f g -> dimap g (either id f) . right'

{- | Action of a coPrism on `Cochoice` `Profunctor`s. -}
mapCoprism
  :: Cochoice p
  => APrism b a t s
  -> p a b
  -> p s t
mapCoprism pat = withPrism pat $ \f g -> unright . dimap (either id f) g

{- | Action of `APartialIso` on `Choice` and `Cochoice` `Profunctor`s. -}
mapPartialIso
  :: (Choice p, Cochoice p)
  => APartialIso s t a b
  -> p a b
  -> p s t
mapPartialIso pat = withPartialIso pat dimapMaybe

{- | Action of `AnIso` on `Profunctor`s. -}
mapIso :: Profunctor p => AnIso s t a b -> p a b -> p s t
mapIso i = withIso i dimap

{- | `_Satisfy` is the prototypical proper partial isomorphism,
identifying a subset which satisfies a predicate. -}
_Satisfy :: (a -> Bool) -> PartialIso' a a
_Satisfy f = partialIso satiate satiate where
  satiate a = if f a then Just a else Nothing

{- | `_Normal` is the prototypical improper isomorphism,
identifying every term with one particular "normal" value. -}
_Normal :: a -> Iso' a ()
_Normal a = iso (const ()) (const a) where

{- | A useful isomorphism identifying `Maybe` and `Either` @()@. -}
_M2E :: Iso (Maybe a) (Maybe b) (Either () a) (Either () b)
_M2E = iso (maybe (Left ()) Right) (either (pure Nothing) Just)

_Null :: (AsEmpty s, AsEmpty t) => PartialIso s t () ()
_Null = partialIso empA empB where
  empA s = if isn't _Empty s then Nothing else Just ()
  empB _ = Just Empty

_NotNull :: (AsEmpty s, AsEmpty t) => PartialIso s t s t
_NotNull = partialIso nonEmp nonEmp where
  nonEmp s = if isn't _Empty s then Just s else Nothing

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
    . crossPartialIso id _Null
    . unit'

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
    . crossPartialIso _Null id
    . unit'

difoldr'
  ::  APrism' (a,c) c
  -> Prism' ([a],c) c
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

dichainl
  :: (Alternator p, Filtrator p)
  => p a b -> p () () -> APartialIso a b (a,a) (b,b) -> p a b
dichainl p sep pat =
  mapPartialIso (coPartialIso (difoldl (coPartialIso pat))) $
    p >*< manyP (sep >* p)

dichainr
  :: (Alternator p, Filtrator p)
  => p a b -> p () () -> APartialIso a b (a,a) (b,b) -> p a b
dichainr p sep pat =
  mapPartialIso (coPartialIso (difoldr (coPartialIso pat))) $
    manyP (p *< sep) >*< p
