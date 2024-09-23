{- |
Module      :  Data.Profunctor.Partial
Description :  choice & cochoice profunctors
Copyright   :  (C) 2024 - Eitan Chatav
License     :  BSD-style (see the file LICENSE)
Maintainer  :  Eitan Chatav <eitan.chatav@gmail.com>
Stability   :  provisional
Portability :  non-portable

This module defines types and terms for
`Choice` and `Cochoice` `Profunctor`s.
-}
module Data.Profunctor.Partial
  ( dimapMaybe
  , alternate
  , discriminate
  , mapMaybeP
  , catMaybesP
  , filterP
  , Partial (..)
  , foldPartial
  ) where

import Control.Lens
import Control.Monad
import Data.Profunctor
import Data.Quiver.Functor
import Witherable

{- |
`Choice` and `Cochoice` profunctors generalize
`Filterable` functors.

`dimapMaybe` is the structural method for
`Choice` and `Cochoice` profunctors,
as `mapMaybe` is for `Filterable` functors.
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

{- | `mapMaybeP` is for `Choice` and `Cochoice`
as `mapMaybe` is for `Filterable`.
-}
mapMaybeP
  :: (Choice p, Cochoice p)
  => (b -> Maybe t)
  -> p a b -> p a t
mapMaybeP = dimapMaybe Just

{- | `catMaybesP` is for `Choice` and `Cochoice`
as `catMaybes` is for `Filterable`.
-}
catMaybesP
  :: (Choice p, Cochoice p)
  => p a (Maybe b) -> p a b
catMaybesP = mapMaybeP id

{- | `filterP` is for `Choice` and `Cochoice`
as `Witherable.filter` is for `Filterable`.
-}
filterP
  :: (Choice p, Cochoice p)
  => (b -> Bool) -> p a b -> p a b
filterP f = mapMaybeP $ \a -> if f a then Just a else Nothing

{- | `Partial` is the free `Choice` and `Cochoice` `Profunctor`. -}
data Partial p a b where
  Partial
    :: (a -> Maybe x)
    -> (y -> Maybe b)
    -> p x y -> Partial p a b
instance Functor (Partial p a) where
  fmap = rmap
instance Filterable (Partial p a) where
  mapMaybe = mapMaybeP
  catMaybes = catMaybesP
instance Profunctor (Partial p) where
  dimap f g (Partial f' g' p) =
    Partial (f' . f) (fmap g . g') p
instance Choice (Partial p) where
  left' (Partial f g p) =
    Partial (either f (const Nothing)) (fmap Left . g) p
  right' (Partial f g p) =
    Partial (either (const Nothing) f) (fmap Right . g) p
instance Cochoice (Partial p) where
  unleft (Partial f g p) =
    Partial (f . Left) (either Just (const Nothing) <=< g) p
  unright (Partial f g p) =
    Partial (f . Right) (either (const Nothing) Just <=< g) p
instance QFunctor Partial where
  qmap pq (Partial f g p) = Partial f g (pq p)
instance QPointed Partial where
  qsingle = Partial Just Just
instance QMonad Partial where
  qjoin = foldPartial id

{- | Fold to a `Choice` and `Cochoice` over `Partial`.-}
foldPartial
  :: (Choice q, Cochoice q)
  => (forall x y. p x y -> q x y)
  -> Partial p a b
  -> q a b
foldPartial k = \(Partial f g p) -> dimapMaybe f g (k p)
