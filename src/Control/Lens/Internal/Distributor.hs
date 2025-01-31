{- |
Module      : Control.Lens.Internal.Distributor
Description : bifocals
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Control.Lens.Internal.Distributor
  ( WrappedPF (..)
  , WrappedPFG (..)
  ) where

import Control.Applicative
import Data.Distributive
import Data.Functor.Compose
import Data.Profunctor
import Data.Profunctor.Distributor
import Witherable

newtype WrappedPF p f a b = WrapPF {unWrapPF :: p a (f b)}
instance (Profunctor p, Functor f)
  => Functor (WrappedPF p f a) where fmap = rmap
deriving via Compose (p a) f instance
  (Monoidal p, Applicative f)
    => Applicative (WrappedPF p f a)
deriving via Compose (p a) f instance
  (Profunctor p, forall x. Alternative (p x), Applicative f)
    => Alternative (WrappedPF p f a)
deriving via Compose (p a) f instance
  (Profunctor p, forall x. Functor (p x), Filterable f)
    => Filterable (WrappedPF p f a)
instance (Profunctor p, Functor f)
  => Profunctor (WrappedPF p f) where
    dimap f g (WrapPF p) = WrapPF $ dimap f (fmap g) p
instance (Distributor p, Applicative f)
  => Distributor (WrappedPF p f) where
    zeroP = WrapPF (rmap pure zeroP)
    WrapPF x >+< WrapPF y = WrapPF $
      dialt id (fmap Left) (fmap Right) x y
    -- manyP
    -- optionalP
instance (Applicative f, Choice p)
  => Choice (WrappedPF p f) where
  left' (WrapPF p) = WrapPF $ rmap sequenceL $ left' p
    where
      sequenceL = either (fmap Left) (pure . Right)
  right' (WrapPF p) = WrapPF $ rmap sequenceL $ right' p
    where
      sequenceL = either (pure . Left) (fmap Right)
instance (Profunctor p, Filterable f)
  => Cochoice (WrappedPF p f) where
    unleft (WrapPF p) = WrapPF $
      dimap Left (mapMaybe (either Just (const Nothing))) p
    unright (WrapPF p) = WrapPF $
      dimap Right (mapMaybe (either (const Nothing) Just)) p
instance (Closed p, Distributive f)
  => Closed (WrappedPF p f) where
    closed (WrapPF p) = WrapPF (rmap distribute (closed p))
instance (Alternator p, Alternative f)
  => Alternator (WrappedPF p f) where
    alternate =
      let
        f = WrapPF
          . rmap (either (fmap Left) pure)
          . alternate
          . Left
          . unWrapPF
        g = WrapPF
          . rmap (either pure (fmap Right))
          . alternate
          . Right
          . unWrapPF
      in
        either f g
    -- someP
instance (Filtrator p, Filterable f)
  => Filtrator (WrappedPF p f) where
    filtrate (WrapPF p) =
      let
        fL = Left . mapMaybe (either Just (const Nothing))
        fR = Right . mapMaybe (either (const Nothing) Just)
        (pL,_) = filtrate (rmap fL p)
        (_,pR) = filtrate (rmap fR p)
      in
        ( WrapPF pL
        , WrapPF pR
        )

newtype WrappedPFG p f g a b = WrapPFG {unWrapPFG :: p (f a) (g b)}
instance (Profunctor p, Functor f, Functor g)
  => Functor (WrappedPFG p f g a) where fmap = rmap
deriving via Compose (p (f a)) g instance
  (Monoidal p, Functor f, Applicative g)
    => Applicative (WrappedPFG p f g a)
instance (Profunctor p, Functor f, Functor g)
  => Profunctor (WrappedPFG p f g) where
    dimap f g (WrapPFG p) = WrapPFG $ dimap (fmap f) (fmap g) p
