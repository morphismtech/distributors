{- |
Module      : Control.Lens.Monocle
Description : monocles
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Control.Lens.Monocle
  ( Monocle
  , Monocle'
  , AMonocle
  , AMonocle'
  , monocle
  , mapMonocle
  , ditraversed
  , forevered
  , cloneMonocle
  , withMonocle
  , Monocular (..), runMonocular
  ) where

import Control.Lens hiding (Traversing)
import Control.Lens.Internal.Profunctor
import Data.Distributive
import Data.Profunctor.Distributor

type Monocle s t a b = forall p f.
  (Monoidal p, Applicative f)
    => p a (f b) -> p s (f t)

type Monocle' s a = Monocle s s a a

type AMonocle s t a b =
  Monocular a b a (Identity b) -> Monocular a b s (Identity t)

type AMonocle' s a = AMonocle s s a a

monocle :: Monocular a b s t -> Monocle s t a b
monocle mon = unwrapPafb . runMonocular mon . WrapPafb

mapMonocle :: Monoidal p => AMonocle s t a b -> p a b -> p s t
mapMonocle mon p = withMonocle mon $ \ocular -> runMonocular ocular p

cloneMonocle :: AMonocle s t a b -> Monocle s t a b
cloneMonocle mon = unwrapPafb . mapMonocle mon . WrapPafb

ditraversed :: (Traversable g, Distributive g) => Monocle (g a) (g b) a b
ditraversed = unwrapPafb . replicateP . WrapPafb

forevered :: Monocle s t () b
forevered = unwrapPafb . foreverP . WrapPafb

withMonocle :: AMonocle s t a b -> (Monocular a b s t -> r) -> r
withMonocle mon k =
  k (runIdentity <$> mon (Identity <$> anyToken))

newtype Monocular a b s t = Monocular
  {unMonocular :: forall f. Applicative f => ((s -> a) -> f b) -> f t}
instance Tokenized a b (Monocular a b) where
  anyToken = Monocular ($ id)
instance Profunctor (Monocular a b) where
  dimap f g (Monocular k) =
    Monocular (fmap g . k . (. (. f)))
instance Functor (Monocular a b s) where fmap = rmap
instance Applicative (Monocular a b s) where
  pure t = Monocular (pure (pure t))
  Monocular x <*> Monocular y = Monocular (liftA2 (<*>) x y)

runMonocular :: Monoidal p => Monocular a b s t -> p a b -> p s t
runMonocular (Monocular k) p = k $ \sa -> lmap sa p
