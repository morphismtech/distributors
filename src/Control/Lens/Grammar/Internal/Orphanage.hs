{-# OPTIONS_GHC -Wno-orphans #-}

{- |
Module      : Control.Lens.Grammar.Internal.Orphanage
Description : partial isomorphisms
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable

An orphanage for instances without a home.
-}

module Control.Lens.Grammar.Internal.Orphanage () where

import Control.Applicative hiding (WrappedArrow)
import Control.Applicative qualified as Ap (WrappedArrow)
import Control.Arrow
import Control.Lens
import Control.Lens.Internal.Prism
import Control.Lens.Internal.Profunctor
import Control.Monad
import Data.Bifunctor.Clown
import Data.Bifunctor.Joker
import Data.Bifunctor.Product
import Data.Distributive
import Data.Functor.Compose
import Data.Functor.Contravariant.Divisible
import Data.Profunctor hiding (WrappedArrow)
import Data.Profunctor qualified as Pro (WrappedArrow)
import Data.Profunctor.Cayley
import Data.Profunctor.Composition
import Data.Profunctor.Monad
import Data.Profunctor.Yoneda
import Text.ParserCombinators.ReadP (ReadP)
import Witherable

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
instance Filterable f => Filterable (Star f a) where
  catMaybes (Star f) = Star (catMaybes . f)
instance Monoid r => Applicative (Forget r a) where
  pure _ = Forget mempty
  Forget f <*> Forget g = Forget (f <> g)
instance Filterable (Forget r a) where
  catMaybes (Forget f) = Forget f
instance Decidable f => Applicative (Clown f a) where
  pure _ = Clown conquer
  Clown x <*> Clown y = Clown (divide (id &&& id) x y)
deriving newtype instance Applicative f => Applicative (Joker f a)
deriving newtype instance Alternative f => Alternative (Joker f a)
deriving newtype instance Filterable f => Filterable (Joker f a)
deriving newtype instance Monad m => Monad (Joker m a)
deriving newtype instance MonadFail m => MonadFail (Joker m a)
deriving newtype instance MonadPlus m => MonadPlus (Joker m a)
instance Filterable f => Cochoice (Joker f) where
  unleft (Joker x) = Joker
    (mapMaybe (either Just (const Nothing)) x)
  unright (Joker x) = Joker
    (mapMaybe (either (const Nothing) Just) x)
instance Filterable ReadP where
  catMaybes m = m >>= maybe empty pure
deriving via Compose (p a) f instance
  (Profunctor p, Applicative (p a), Applicative f)
    => Applicative (WrappedPafb f p a)
deriving via Compose (p a) f instance
  (Profunctor p, Alternative (p a), Applicative f)
    => Alternative (WrappedPafb f p a)
instance (Closed p, Distributive f)
  => Closed (WrappedPafb f p) where
    closed (WrapPafb p) = WrapPafb (rmap distribute (closed p))
deriving via (Ap.WrappedArrow p a) instance Arrow p
  => Functor (Pro.WrappedArrow p a)
deriving via (Ap.WrappedArrow p a) instance Arrow p
  => Applicative (Pro.WrappedArrow p a)
deriving via (Pro.WrappedArrow p) instance Arrow p
  => Profunctor (Ap.WrappedArrow p)
instance
  ( forall x. Applicative (p x), Profunctor p
  , Applicative (q a), Profunctor q
  ) => Applicative (Procompose p q a) where
    pure b = Procompose (pure b) (pure b)
    Procompose wb aw <*> Procompose vb av = Procompose
      (liftA2 ($) (lmap fst wb) (lmap snd vb))
      (liftA2 (,) aw av)
instance (forall x. Applicative (p x), forall x. Applicative (q x))
  => Applicative (Product p q a) where
    pure b = Pair (pure b) (pure b)
    Pair x0 y0 <*> Pair x1 y1 = Pair (x0 <*> x1) (y0 <*> y1)
instance (Functor f, Functor (p a)) => Functor (Cayley f p a) where
  fmap f (Cayley x) = Cayley (fmap (fmap f) x)
instance (Applicative f, Applicative (p a)) => Applicative (Cayley f p a) where
  pure b = Cayley (pure (pure b))
  Cayley x <*> Cayley y = Cayley ((<*>) <$> x <*> y)
instance (Profunctor p, Applicative (p a))
  => Applicative (Yoneda p a) where
    pure = proreturn . pure
    ab <*> cd = proreturn (proextract ab <*> proextract cd)
instance (Profunctor p, Applicative (p a))
  => Applicative (Coyoneda p a) where
    pure = proreturn . pure
    ab <*> cd = proreturn (proextract ab <*> proextract cd)
instance (Profunctor p, Alternative (p a))
  => Alternative (Yoneda p a) where
    empty = proreturn empty
    ab <|> cd = proreturn (proextract ab <|> proextract cd)
    many = proreturn . many . proextract
instance (Profunctor p, Alternative (p a))
  => Alternative (Coyoneda p a) where
    empty = proreturn empty
    ab <|> cd = proreturn (proextract ab <|> proextract cd)
    many = proreturn . many . proextract
instance Applicative (Market a b s) where
  pure t = Market (pure t) (pure (Left t))
  Market f0 g0 <*> Market f1 g1 = Market
    (\b -> f0 b (f1 b))
    (\s ->
      case g0 s of
        Left bt -> case g1 s of
          Left b -> Left (bt b)
          Right a -> Right a
        Right a -> Right a
    )
