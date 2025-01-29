module Control.Lens.Monocle
  ( Monocle
  , AMonocle
  , withMonocle
  , mapMonocle
  , cloneMonocle
  , Monocular (..)
  , runMonocular
  ) where

import Control.Lens.Internal.Token
import Data.Functor.Apply
import Data.Profunctor
import Data.Profunctor.Distributor
import Data.Functor.Identity

type Monocle s t a b = forall p f.
  (Monoidal p, Applicative f) => p a (f b) -> p s (f t)

newtype Monocular a b s t = Monocular
  { unMonocular
      :: forall f. Applicative f
      => ((s -> a) -> f b) -> f t
  }
instance Functor (Monocular a b s) where fmap = rmap
instance Apply (Monocular a b s) where
  Monocular x <.> Monocular y = Monocular (\sab -> liftA2 ($) (x sab) (y sab))
instance Applicative (Monocular a b s) where
  pure t = Monocular (\_ -> pure t)
  (<*>) = (<.>)
instance Profunctor (Monocular a b) where
  dimap f g (Monocular k) = Monocular (fmap g . k . (. (. f)))
instance Monoidal1 (Monocular a b)
instance Monoidal (Monocular a b)
instance Tokenized a b (Monocular a b) where
  anyToken = Monocular ($ id)

runMonocular
  :: Monoidal p
  => Monocular a b s t
  -> ((s -> a) -> p a b)
  -> p s t
runMonocular (Monocular k) f =
  unWrapP . k $ \sa -> WrapP (lmap sa (f sa))

type AMonocle s t a b =
  Monocular a b a (Identity b) -> Monocular a b s (Identity t)

withMonocle :: AMonocle s t a b -> (Monocular a b s t -> r) -> r
withMonocle mon k =
  k (runIdentity <$> mon (Identity <$> anyToken))

mapMonocle :: Monoidal p => AMonocle s t a b -> p a b -> p s t
mapMonocle mon p = withMonocle mon $ \eye ->
  runMonocular eye $ \_ -> p

cloneMonocle :: AMonocle s t a b -> Monocle s t a b
cloneMonocle mon = unWrapPf . mapMonocle mon . WrapPf
