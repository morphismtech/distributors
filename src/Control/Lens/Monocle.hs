{- |
Module      :  Control.Lens.Monocle
Description :  monocles
Copyright   :  (C) 2024 - Eitan Chatav
License     :  BSD-style (see the file LICENSE)
Maintainer  :  Eitan Chatav <eitan.chatav@gmail.com>
Stability   :  provisional
Portability :  non-portable

`Monocle`s
It also provides functions which define
`Control.Lens.Traversal.Traversal` optics
in a profunctor representation using `Strong` and `Choice`,
`Monoidal` `Profunctor`s. It also defines the `Monocle`
optic which combines `Traversal`s and `Cotraversal`s.
-}
module Control.Lens.Monocle
  ( Monocle
  , AMonocle
  , withMonocle
  , (>..<)
  , cloneMonocle
  , monGrate
  , monTraversal
  , monCotraversal
  , monBitraversal
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

cloneMonocle :: AMonocle s t a b -> Monocle s t a b
cloneMonocle mon
  = lmap Identity
  . runBiff
  . (mon >..<)
  . Biff
  . lmap runIdentity

monTraversal :: AMonocle s t a b -> Traversal s t a b
monTraversal mon = runStar . (mon >..<) . Star

monocle0 :: Monocle () () a b
monocle0 _ = pureP (pure ())

monocle2 :: Monocle (a,a) (b,b) a b
monocle2 p = dimap2 fst snd (liftA2 (,)) p p

monCotraversal :: Functor f => AMonocle s t a b -> (f a -> b) -> f s -> t
monCotraversal mon = runCostar . (mon >..<) . Costar

monGrate :: Closed p => AMonocle s t a b -> p a b -> p s t
monGrate mon = dimap (&) ((monCotraversal mon buy) . Purchase) . closed

monBitraversal
  :: (Functor f, Applicative g)
  => AMonocle s t a b
  -> (f a -> g b) -> f s -> g t
monBitraversal mon = runBiff . (mon >..<) . Biff
