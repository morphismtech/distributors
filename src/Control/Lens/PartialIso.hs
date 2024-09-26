{- |
Module      :  Control.Lens.PartialIso
Description :  partial isomorphisms
Copyright   :  (C) 2024 - Eitan Chatav
License     :  BSD-style (see the file LICENSE)
Maintainer  :  Eitan Chatav <eitan.chatav@gmail.com>
Stability   :  provisional
Portability :  non-portable

This module defines types and terms for
the partial isomorphism optic `PartialIso`,
a weakening of `Control.Lens.Prism.Prism`.
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
  , (>?)
  , (?<)
  , (>?<)
  , mapIso
  , coPrism
    -- * Common (Partial)Isos
  , _Satisfy
  , _Normal
  , _M2E
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.Internal.FunList
import Control.Monad
import Data.Profunctor
import Data.Profunctor.Partial
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
  mapMaybe = mapMaybeP
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
(>?)
  :: Choice p
  => APrism s t a b
  -> p a b
  -> p s t
(>?) pat = withPrism pat $ \f g -> dimap g (either id f) . right'
infixr 2 >?

{- | Action of a coPrism on `Cochoice` `Profunctor`s. -}
(?<)
  :: Cochoice p
  => APrism b a t s
  -> p a b
  -> p s t
(?<) pat = withPrism pat $ \f g -> unright . dimap (either id f) g
infixr 2 ?<

{- | Clone `APrism` into a `coPrism` `Optic`.
-}
coPrism
  :: (Profunctor p, Filterable f)
  => APrism b a t s
  -> Optic p f s t a b
coPrism pat = runPafb . (pat ?<) . Pafb

{- | Action of `APartialIso` on `Choice` and `Cochoice` `Profunctor`s. -}
(>?<)
  :: (Choice p, Cochoice p)
  => APartialIso s t a b
  -> p a b
  -> p s t
i >?< p = withPartialIso i $ \f g -> dimapMaybe f g p
infixr 2 >?<

{- | Action of `AnIso` on `Profunctor`s. -}
mapIso :: Profunctor p => AnIso s t a b -> p a b -> p s t
mapIso i p = withIso i $ \here there -> dimap here there p

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
