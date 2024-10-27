module Control.Lens.Wither
  ( Wither
  , AWither
  , Withering (..)
  ) where

import Control.Applicative
import Data.Functor.Alt

type Wither s t a b =
  forall f. Alternative f => (a -> f b) -> s -> f t

type AWither s t a b =
  (a -> Withering (->) a b b) -> s -> Withering (->) a b t

newtype Withering p a b t = Withering
  { runWithering :: forall f. Alternative f => p a (f b) -> f t }
instance Functor (Withering p a b) where
  fmap f (Withering k) = Withering (fmap f . k)
instance Apply (Withering p a b) where
  (<.>) = (<*>)
  (.>) = (*>)
  (<.) = (<*)
instance Applicative (Withering p a b) where
  pure a = Withering $ \_ -> pure a
  Withering f <*> Withering a = Withering $ \ pafb -> f pafb <*> a pafb
  liftA2 f (Withering x) (Withering y) =
    Withering $ \pafb -> liftA2 f (x pafb) (y pafb)
  Withering x *> Withering y = Withering $ \pafb -> x pafb *> y pafb
  Withering x <* Withering y = Withering $ \pafb -> x pafb <* y pafb
instance Alt (Withering p a b) where
  Withering x <!> Withering y = Withering $ \ pafb -> x pafb <|> y pafb
instance Alternative (Withering p a b) where
  empty = Withering $ \_ -> empty
  (<|>) = (<!>)
