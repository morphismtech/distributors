{- |
Module      :  Control.Lens.PartialIso
Description :  choice & cochoice profunctors, and partial isomorphisms
Copyright   :  (C) 2024 - Eitan Chatav
License     :  BSD-style (see the file LICENSE)
Maintainer  :  Eitan Chatav <eitan.chatav@gmail.com>
Stability   :  provisional
Portability :  non-portable

This module defines types and terms for
`Choice` and `Cochoice` `Profunctor`s as well as
the partial isomorphism optic `PartialIso`,
a weakening of `Control.Lens.Prism.Prism`.
-}
module Control.Lens.PartialIso
  ( -- * Choice and Cochoice Profunctors
    dimapMaybe
  , alternate
  , discriminate
  , mapMaybeP
  , catMaybesP
  , filterP
    -- * Partial Isomorphisms
  , PartialIso
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
    -- * Prism, Coprism and Partial Isomorphism Actions
  , (>?)
  , (?<)
  , (>?<)
    -- * Common (Partial) Isomorphisms
  , _Guard
  , _Normal
  , _M2E
    -- * ChooseApF
  , ChooseApF (..)
  ) where

import Control.Applicative
import Control.Lens
import Control.Monad
import Data.Kind
import Data.Profunctor
import Data.Profunctor.Monad
import Witherable

{- | A `Choice` and `Cochoice` `Profunctor`
exhibits an action `>?<` of partial isomorphisms.
They are analagous to `Filterable` `Functor`s.

prop> i >?< p = withPartialIso i $ \f g -> dimapMaybe f g p

`dimapMaybe` is the structural morphism for `Choice` and `Cochoice`
profunctors.
-}
dimapMaybe
  :: (Choice p, Cochoice p)
  => (s -> Maybe a) -> (b -> Maybe t)
  -> p a b -> p s t
dimapMaybe f g =
  let
    m2e h = view _M2E . h
    fg = dimap (>>= m2e f) (>>= m2e g)
  in
    unright . fg . right'

{- | `Choice` and `Cochoice` profunctors
generalize the `Choice` methods
with the `alternate` function.

prop> left' = alternate . Left
prop> right' = alternate . Right

`alternate` has less general constraint
but a more general type,
than `left'` `Control.Arrow.|||` `right'`.

>>> :type left' ||| right'
left' ||| right'
  :: Choice p =>
     Either (p a a) (p c c) -> p (Either a c) (Either a c)
-}
alternate
  :: (Choice p, Cochoice p)
  => Either (p a b) (p c d)
  -> p (Either a c) (Either b d)
alternate (Left p) =
  dimapMaybe (either Just (pure Nothing)) (Just . Left) p
alternate (Right p) =
  dimapMaybe (either (pure Nothing) Just) (Just . Right) p

{-| `Choice` and `Cochoice` profunctors
generalize the `Cochoice` methods
with the `discriminate` function.

prop> unleft = fst . discriminate
prop> unright = snd . discriminate

`discriminate` has less general constraint
but a more general type,
than `unleft` `Control.Arrow.&&&` `unright`.

>>> :type unleft &&& unright
unleft &&& unright
  :: Cochoice p => p (Either a d) (Either a d) -> (p a a, p d d)
-}
discriminate
  :: (Choice p, Cochoice p)
  => p (Either a c) (Either b d)
  -> (p a b, p c d)
discriminate p =
  ( dimapMaybe (Just . Left) (either Just (pure Nothing)) p
  , dimapMaybe (Just . Right) (either (pure Nothing) Just) p
  )

{- | `mapMaybeP` for `Choice` and `Cochoice` `Profunctor`s
is the analague to `mapMaybe` for `Filterable` `Functor`s.
-}
mapMaybeP
  :: (Choice p, Cochoice p)
  => (b -> Maybe t)
  -> p a b -> p a t
mapMaybeP = dimapMaybe Just

{- | `catMaybesP` for `Choice` and `Cochoice` `Profunctor`s
is the analague to `catMaybes` for `Filterable` `Functor`s.
-}
catMaybesP
  :: (Choice p, Cochoice p)
  => p a (Maybe b) -> p a b
catMaybesP = mapMaybeP id

{- | `filterP` for `Choice` and `Cochoice` `Profunctor`s
is the analague to `Witherable.filter` for `Filterable` `Functor`s.
-}
filterP
  :: (Choice p, Cochoice p)
  => (b -> Bool) -> p a b -> p a b
filterP f = mapMaybeP $ \a -> if f a then Just a else Nothing

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
instance Monoid a => Applicative (PartialExchange a b s) where
  pure t = PartialExchange (\_ -> mempty) (\_ -> Just t)
  PartialExchange f' g' <*> PartialExchange f g = PartialExchange
    (\s -> (<>) <$> f' s <*> f s)
    (\b -> g' b <*> g b)
instance Monoid a => Alternative (PartialExchange a b s) where
  empty = mempty
  (<|>) = (<>)
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

{- | Convert `APartialIso` to the pair of
functions that characterize it. -}
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
i >? p = withPrism i $ \f g -> dimap g (either id f) (right' p)
infixr 2 >?

{- | Action of a coprism on `Cochoice` `Profunctor`s. -}
(?<)
  :: Cochoice p
  => APrism b a t s
  -> p a b
  -> p s t
i ?< p = withPrism i $ \f g -> unright (dimap (either id f) g p)
infixr 2 ?<

{- | Action of `APartialIso` on `Choice` and `Cochoice` `Profunctor`s. -}
(>?<)
  :: (Choice p, Cochoice p)
  => APartialIso s t a b
  -> p a b
  -> p s t
i >?< p = withPartialIso i $ \f g -> dimapMaybe f g p
infixr 2 >?<

{- | `_Guard` is the prototypical proper partial isomorphism,
identifying a subset which satisfies a predicate. -}
_Guard :: (a -> Bool) -> PartialIso' a a
_Guard f = partialIso satiate satiate where
  satiate a = if f a then Just a else Nothing

{- | `_Normal` is the prototypical improper isomorphism,
identifying every term with one particular "normal" value. -}
_Normal :: a -> Iso' a ()
_Normal a = iso (const ()) (const a) where

{- | A useful isormorphism identifying `Maybe` and `Either` @()@. -}
_M2E :: Iso (Maybe a) (Maybe b) (Either () a) (Either () b)
_M2E = iso (maybe (Left ()) Right) (either (pure Nothing) Just)

type ChooseApF
  :: ((Type -> Type -> Type) -> (Type -> Type -> Type))
     -- ^ choice of free `Monoidal`
  -> (Type -> Type -> Type)
     -- ^ base quiver
  -> Type -> Type -> Type
data ChooseApF mon p a b where
  ChooseNil :: ChooseApF mon p a b
  ChoosePure :: b -> ChooseApF mon p a b
  ChooseAp
    :: (a -> Maybe s)
    -> ChooseApF mon p a (t -> Maybe b)
    -> p s t
    -> ChooseApF mon p a b
instance Functor (ChooseApF mon p a) where fmap = rmap
instance Filterable (ChooseApF mon p a) where
  mapMaybe = mapMaybeP
instance Applicative (ChooseApF mon p a) where
  pure = ChoosePure
  ChooseNil <*> _ = ChooseNil
  ChoosePure f <*> x = f <$> x
  ChooseAp f g x <*> y =
    let
      apply h a t = ($ a) <$> h t
    in
      ChooseAp f (apply <$> g <*> y) x
instance Profunctor (ChooseApF mon p) where
  dimap _ _ ChooseNil = ChooseNil
  dimap _ g (ChoosePure b) = ChoosePure (g b)
  dimap f' g' (ChooseAp f g x) =
    ChooseAp (f . f') ((fmap g' .) <$> lmap f' g) x
instance Choice (ChooseApF mon p) where
  left' ChooseNil = ChooseNil
  left' (ChoosePure b) = ChoosePure (Left b)
  left' (ChooseAp f g x) =
    let
      apply e t = either ((Left <$>) . ($ t)) (Just . Right) e
    in
      ChooseAp (either f (pure Nothing)) (apply <$> (left' g)) x
  right' ChooseNil = ChooseNil
  right' (ChoosePure b) = ChoosePure (Right b)
  right' (ChooseAp f g x) =
    let
      apply e t = either (Just . Left) ((Right <$>) . ($ t)) e
    in
      ChooseAp (either (pure Nothing) f) (apply <$> (right' g)) x
instance Cochoice (ChooseApF mon p) where
  unleft ChooseNil = ChooseNil
  unleft (ChoosePure (Left b)) = ChoosePure b
  unleft (ChoosePure (Right _)) = ChooseNil
  unleft (ChooseAp f g x) =
    let
      g' = (Left . (either Just (pure Nothing) <=<)) <$> g
    in
      ChooseAp (f . Left) (unleft g') x
  unright ChooseNil = ChooseNil
  unright (ChoosePure (Left _)) = ChooseNil
  unright (ChoosePure (Right b)) = ChoosePure b
  unright (ChooseAp f g x) =
    let
      g' = (Right . (either (pure Nothing) Just <=<)) <$> g
    in
      ChooseAp (f . Right) (unright g') x
instance ProfunctorFunctor (ChooseApF mon) where
  promap _ ChooseNil = ChooseNil
  promap _ (ChoosePure b) = ChoosePure b
  promap h (ChooseAp f g x) = ChooseAp f (promap h g) (h x)
