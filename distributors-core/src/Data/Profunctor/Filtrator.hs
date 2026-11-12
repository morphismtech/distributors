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

import Control.Arrow
import Control.Lens.PartialIso
import Control.Lens.Internal.Profunctor
import Control.Monad
import Data.Bifunctor.Joker
import Data.Monoid.Disjunctive (falseP)
import Data.Profunctor
import Data.Profunctor.Distributor
import Data.Profunctor.Monad
import Data.Profunctor.Monadic (Monadic)
import Data.Profunctor.Yoneda
import Witherable

{- | The `Filtrator` class extends `Cochoice`,
as well as `Filterable`, adding the `filtrate` method,
which projects a profunctor of sums onto its summands.

For a `Data.Profunctor.Monoidal.Cocartesian.CocartesianChoice`,
`filtrate` is a retraction of `Data.Profunctor.Monoidal.Cocartesian.alternate`,
projecting a summand back out of its injection,

> prop> fst (filtrate (alternate (Left p))) = p
> prop> snd (filtrate (alternate (Right p))) = p

that is, since `unleft` is @fst . filtrate@ & `left'` is @alternate . Left@,

> prop> unleft . left' = id
> prop> unright . right' = id

`filtrate` isn't a retraction of
`Data.Profunctor.Monoidal.Cocartesian.>+<` in general, though,
since it tries its summands in turn, & the second summand
of a left-biased or predictive one,
like the @Parsor s Maybe@ or @Parsector@ parsers of @distributors-grammar@,
is lost where the first applies. Nor is `Data.Profunctor.Monoidal.Cocartesian.>+<`
a retraction of `filtrate`, since a profunctor of sums may cross summands,
as @rmap (either Right Left)@ does.
-}
class (Cochoice p, forall x. Filterable (p x))
  => Filtrator p where

    {- |
    > prop> unleft = fst . filtrate
    > prop> unleft = lmap Left . mapMaybe (either Just (const Nothing))
    > prop> unright = snd . filtrate
    > prop> unright = lmap Right . mapMaybe (either (const Nothing) Just)

    `filtrate` is a distant relative to `Data.Either.partitionEithers`.
    `filtrate` can be given a default value for `Monadic`
    `Alternator`s via `mfiltrate`.

    > prop> filtrate = mfiltrate

    `filtrate` has a default for `Choice` & `Cochoice` partial profunctors.
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

-- | A `Monadic` `Alternator` has
-- an equivalent to `filtrate`, given by `mfiltrate`.
--
-- > prop> filtrate = mfiltrate
--
mfiltrate
  :: (Monadic p, Alternator p)
  => p (Either a c) (Either b d) -- ^ partition `Either`
  -> (p a b, p c d)
mfiltrate =
  (lmap Left >=> either pure (const falseP))
  &&&
  (lmap Right >=> either (const falseP) pure)

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
instance Filtrator (PartialExchange a b) where
  filtrate (PartialExchange f g) =
    ( PartialExchange (f . Left) (either Just (pure Nothing) <=< g)
    , PartialExchange (f . Right) (either (pure Nothing) Just <=< g)
    )
instance Filterable f => Filtrator (Joker f) where
  filtrate (Joker x) =
    ( Joker (mapMaybe (either Just (const Nothing)) x)
    , Joker (mapMaybe (either (const Nothing) Just) x)
    )
