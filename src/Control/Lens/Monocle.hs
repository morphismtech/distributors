{- |
Module      :  Control.Lens.Monocle
Description :  monocles
Copyright   :  (C) 2024 - Eitan Chatav
License     :  BSD-style (see the file LICENSE)
Maintainer  :  Eitan Chatav <eitan.chatav@gmail.com>
Stability   :  provisional
Portability :  non-portable

`Monocle`s are optics that combine `Traversal`s and
cotraversals, also known as grates.
-}
module Control.Lens.Monocle
  ( Monocle
  , AMonocle
  , withMonocle
  , (>..<)
  , monBitraversal
  , cloneMonocle
  , monTraversal
  , monCotraversal
  , monGrate
  , monocle0
  , monocle2
  ) where

import Control.Lens hiding (index, Traversing)
import Control.Lens.Internal.Context
import Data.Bifunctor.Biff
import Data.Profunctor
import Data.Profunctor.Monoidal

type Monocle s t a b = forall p f.
  (Monoidal p, Applicative f) => p a (f b) -> p s (f t)

type AMonocle s t a b =
  Shop a b a (Identity b) -> Shop a b s (Identity t)

withMonocle :: AMonocle s t a b -> (Shop a b s t -> r) -> r
withMonocle mon k =
  k (runIdentity <$> mon (Identity <$> Shop (sell id)))

(>..<) :: Monoidal p => AMonocle s t a b -> p a b -> p s t
mon >..< p = withMonocle mon (\sh -> runShop sh (\_ -> p))

monBitraversal
  :: (Functor f, Applicative g, Monoidal p)
  => AMonocle s t a b
  -> p (f a) (g b) -> p (f s) (g t)
monBitraversal mon = runBiff . (mon >..<) . Biff

cloneMonocle :: AMonocle s t a b -> Monocle s t a b
cloneMonocle mon
  = lmap Identity
  . monBitraversal mon
  . lmap runIdentity

monTraversal :: AMonocle s t a b -> Traversal s t a b
monTraversal = cloneMonocle

monCotraversal
  :: (Functor f, Monoidal p)
  => AMonocle s t a b -> p (f a) b -> p (f s) t
monCotraversal mon
  = rmap runIdentity
  . monBitraversal mon
  . rmap Identity

monGrate :: Closed p => AMonocle s t a b -> p a b -> p s t
monGrate mon = dimap (&) (monCotraversal mon buy . Purchase) . closed

monocle0 :: Monocle () () a b
monocle0 _ = pureP (pure ())

monocle2 :: Monocle (a,a) (b,b) a b
monocle2 p = dimap2 fst snd (liftA2 (,)) p p
