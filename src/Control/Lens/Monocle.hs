{- |
Module      : Control.Lens.Monocle
Description : monocles
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable

See Oliveira, Jaskelioff & de Melo,
[On Structuring Functional Programs with Monoidal Profunctors](https://arxiv.org/abs/2207.00852)
-}

module Control.Lens.Monocle
  ( Monocle
  , AMonocle
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

{- | `Monocle`s are an optic that generalizes
`Control.Lens.Traversal.Traversal`s & `Control.Lens.Grate.Grate`s.

Every `Control.Lens.Iso.Iso` is a `Monocle`.

`Monocle`s are isomorphic to `Monocular`s.
-}
type Monocle s t a b = forall p f.
  (Monoidal p, Applicative f)
    => p a (f b) -> p s (f t)

{- | If you see this in a signature for a function,
the function is expecting a `Monocle`. -}
type AMonocle s t a b =
  Monocular a b a (Identity b) -> Monocular a b s (Identity t)

{- | Build a `Monocle` from a concrete `Monocular`. -}
monocle :: Monocular a b s t -> Monocle s t a b
monocle mon = unwrapPafb . runMonocular mon . WrapPafb

{- | Action of `AMonocle` on `Monoidal` `Profunctor`s. -}
mapMonocle :: Monoidal p => AMonocle s t a b -> p a b -> p s t
mapMonocle mon p = withMonocle mon $ \f -> lmap f p

{- | Clone `AMonocle` so that you can reuse the same
monomorphically typed monocle for different purposes.
-}
cloneMonocle :: AMonocle s t a b -> Monocle s t a b
cloneMonocle mon = unwrapPafb . mapMonocle mon . WrapPafb

{- |
prop> traverse = ditraversed
prop> cotraversed = ditraversed
-}
ditraversed :: (Traversable g, Distributive g) => Monocle (g a) (g b) a b
ditraversed = unwrapPafb . replicateP . WrapPafb

{- | Repeat action indefinitely. -}
forevered :: Monocle s t () b
forevered = unwrapPafb . foreverP . WrapPafb

{- | Run `AMonocle` over an `Applicative`. -}
withMonocle :: Applicative f => AMonocle s t a b -> ((s -> a) -> f b) -> f t
withMonocle mon = unMonocular (runIdentity <$> mon (Identity <$> anyToken))

{- | `Monocular` provides an efficient
concrete representation of `Monocle`s. -}
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

{- | Run a `Monocular` on a `Monoidal` `Profunctor`. -}
runMonocular :: Monoidal p => Monocular a b s t -> p a b -> p s t
runMonocular (Monocular k) p = k $ \f -> lmap f p
