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
module Data.Profunctor.Partial1
  ( dimapMaybe
  , Partial (Partial)
  , foldPartial
  , Filtrator (filtrate)
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

class (Cochoice p, forall x. Filterable (p x))
  => Filtrator p where
    filtrate :: p (Either a c) (Either b d) -> (p a b, p c d)
    default filtrate
      :: Choice p => p (Either a c) (Either b d) -> (p a b, p c d)
    filtrate p =
      ( dimapMaybe (Just . Left) (either Just (pure Nothing)) p
      , dimapMaybe (Just . Right) (either (pure Nothing) Just) p
      )

{- | `Partial` is the free `Choice` and `Cochoice` `Profunctor`. -}
data Partial p a b where
  Partial
    :: (a -> Maybe x)
    -> (y -> Maybe b)
    -> p x y -> Partial p a b
instance Functor (Partial p a) where
  fmap = rmap
instance Filterable (Partial p a) where
  mapMaybe = dimapMaybe Just
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
instance Filtrator (Partial p)
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
