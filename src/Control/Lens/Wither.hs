{- |
Module      : Control.Lens.Wither
Description : monocles
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Control.Lens.Wither
  ( Wither
  , Wither'
  , AWither
  , AWither'
  , cloneWither
  , Zabar (..)
  ) where

import Control.Applicative
import Control.Lens.Internal.Context
import Data.Profunctor.Rep
import Data.Profunctor.Sieve
import Prelude hiding (filter)

type Wither s t a b = forall f.
  Alternative f => (a -> f b) -> s -> f t

type Wither' s a = Wither s s a a

type AWither s t a b =
  (a -> Zabar (->) a b b) -> s -> Zabar (->) a b t

type AWither' s a = AWither s s a a

cloneWither :: AWither s t a b -> Wither s t a b
cloneWither w f = (\g (Zabar k) -> k g) f . w sell

newtype Zabar p a b t = Zabar
  { runZabar :: forall f. Alternative f => p a (f b) -> f t }
instance Functor (Zabar p a b) where
  fmap f (Zabar k) = Zabar (fmap f . k)
instance Applicative (Zabar p a b) where
  pure a = Zabar $ \_ -> pure a
  Zabar mf <*> Zabar ma = Zabar $ \ pafb -> mf pafb <*> ma pafb
instance Alternative (Zabar p a b) where
  empty = Zabar $ \_ -> empty
  Zabar mx <|> Zabar my = Zabar $ \ pafb -> mx pafb <|> my pafb
instance Corepresentable p => Sellable p (Zabar p) where
  sell = cotabulate $ \w -> Zabar
       $   tabulate $ \k -> pure (cosieve k w)
