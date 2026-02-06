{-|
Module      : Data.Profunctor.Filtrator
Description : filtrators
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Data.Profunctor.Filtrator
  ( -- * Filtrator
    Filtrator (filtrate)
  , mfiltrate
  ) where

import Control.Applicative
import Control.Arrow
import Control.Lens.PartialIso
import Control.Lens.Internal.Profunctor
import Control.Monad
import Data.Profunctor
import Data.Profunctor.Distributor
import Data.Profunctor.Monad
import Data.Profunctor.Monadic (Monadic)
import Data.Profunctor.Yoneda
import Witherable

{- | The `Filtrator` class extends `Cochoice`,
as well as `Filterable`, adding the `filtrate` method,
which is an oplax monoidal structure morphism dual to `>+<`.

prop> filtrate . uncurry (>+<) = id
prop> uncurry (>+<) . filtrate = id
-}
class (Cochoice p, forall x. Filterable (p x))
  => Filtrator p where

    {- |
    prop> unleft = fst . filtrate
    prop> unright = snd . filtrate

    `filtrate` is a distant relative to `Data.Either.partitionEithers`.

    `filtrate` has a default for `Choice`.
    -}
    filtrate
      :: p (Either a c) (Either b d)
      -> (p a b, p c d)
    default filtrate
      :: Choice p
      => p (Either a c) (Either b d)
      -> (p a b, p c d)
    filtrate =
      dimapMaybe (Just . Left) (either Just (const Nothing))
      &&&
      dimapMaybe (Just . Right) (either (const Nothing) Just)

-- | `mfiltrate` can be used as `filtrate`, for `Monadic` `Alternator`s.
--
-- prop> mfiltrate = filtrate
mfiltrate
  :: (Monadic p, Alternator p)
  => p (Either a c) (Either b d)
  -> (p a b, p c d)
mfiltrate =
  (lmap Left >=> either pure (const empty))
  &&&
  (lmap Right >=> either (const empty) pure)

instance (Profunctor p, forall x. Functor (p x), Filterable f)
  => Filtrator (WrappedPafb f p) where
    filtrate (WrapPafb p) =
      ( WrapPafb $ dimap Left (mapMaybe (either Just (const Nothing))) p
      , WrapPafb $ dimap Right (mapMaybe (either (const Nothing) Just)) p
      )
instance Filtrator p => Filtrator (Coyoneda p) where
  filtrate p =
    let (q,r) = filtrate (proextract p)
    in (proreturn q, proreturn r)
instance Filtrator p => Filtrator (Yoneda p) where
  filtrate p =
    let (q,r) = filtrate (proextract p)
    in (proreturn q, proreturn r)
instance Filtrator (Forget r) where
  filtrate (Forget f) = (Forget (f . Left), Forget (f . Right))
instance (Filterable f, Traversable f) => Filtrator (Star f) where
  filtrate (Star f) =
    ( Star (mapMaybe (either Just (const Nothing)) . f . Left)
    , Star (mapMaybe (either (const Nothing) Just) . f . Right)
    )
instance Filtrator (PartialExchange a b) where
  filtrate (PartialExchange f g) =
    ( PartialExchange (f . Left) (either Just (pure Nothing) <=< g)
    , PartialExchange (f . Right) (either (pure Nothing) Just <=< g)
    )
