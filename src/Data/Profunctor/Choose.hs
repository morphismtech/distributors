{- |
Module      :  Data.Profunctor.Choose
Description :  choice & cochoice profunctors
Copyright   :  (C) 2024 - Eitan Chatav
License     :  BSD-style (see the file LICENSE)
Maintainer  :  Eitan Chatav <eitan.chatav@gmail.com>
Stability   :  provisional
Portability :  non-portable

This module defines types and terms for
`Choice` and `Cochoice` `Profunctor`s.
-}
module Data.Profunctor.Choose
  ( dimapMaybe
  , alternate
  , discriminate
  , mapMaybeP
  , catMaybesP
  , filterP
  , Choose (..)
  , foldChoose
  ) where

import Control.Lens
import Control.Monad
import Data.Profunctor
import Data.Quiver.Functor
import Witherable

{- | A `Choice` and `Cochoice` `Profunctor`
exhibits an action `>?<` of partial isomorphisms.
They are analogous to `Filterable` `Functor`s.

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

{- | `mapMaybeP` for `Choice` and `Cochoice` `Profunctor`s
is the analog to `mapMaybe` for `Filterable` `Functor`s.
-}
mapMaybeP
  :: (Choice p, Cochoice p)
  => (b -> Maybe t)
  -> p a b -> p a t
mapMaybeP = dimapMaybe Just

{- | `catMaybesP` for `Choice` and `Cochoice` `Profunctor`s
is the analog to `catMaybes` for `Filterable` `Functor`s.
-}
catMaybesP
  :: (Choice p, Cochoice p)
  => p a (Maybe b) -> p a b
catMaybesP = mapMaybeP id

{- | `filterP` for `Choice` and `Cochoice` `Profunctor`s
is the analog to `Witherable.filter` for `Filterable` `Functor`s.
-}
filterP
  :: (Choice p, Cochoice p)
  => (b -> Bool) -> p a b -> p a b
filterP f = mapMaybeP $ \a -> if f a then Just a else Nothing

{- | `Choose` is the free `Choice` and `Cochoice` `Profunctor`. -}
data Choose p a b where
  Choose
    :: (a -> Maybe x)
    -> (y -> Maybe b)
    -> p x y -> Choose p a b
instance Functor (Choose p a) where
  fmap = rmap
instance Filterable (Choose p a) where
  mapMaybe = mapMaybeP
  catMaybes = catMaybesP
instance Profunctor (Choose p) where
  dimap f g (Choose f' g' p) =
    Choose (f' . f) (fmap g . g') p
instance Choice (Choose p) where
  left' (Choose f g p) =
    Choose (either f (const Nothing)) (fmap Left . g) p
  right' (Choose f g p) =
    Choose (either (const Nothing) f) (fmap Right . g) p
instance Cochoice (Choose p) where
  unleft (Choose f g p) =
    Choose (f . Left) (either Just (const Nothing) <=< g) p
  unright (Choose f g p) =
    Choose (f . Right) (either (const Nothing) Just <=< g) p
instance QFunctor Choose where
  qmap pq (Choose f g p) = Choose f g (pq p)
instance QPointed Choose where
  qsingle = Choose Just Just
instance QMonad Choose where
  qjoin = foldChoose id

foldChoose
  :: (Choice q, Cochoice q)
  => (forall x y. p x y -> q x y)
  -> Choose p a b
  -> q a b
foldChoose k = \(Choose f g p) -> dimapMaybe f g (k p)
