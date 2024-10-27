module Control.Lens.Bifocal1
  ( Bifocal
  , ABifocal
  , Binocular (..)
  ) where

import Control.Lens.Internal.Token
import Data.Functor.Alt
import Data.Functor.Identity
import Data.Profunctor
import Data.Profunctor.Distributor1

type Bifocal s t a b = forall p f.
  (Alternator1 p, Applicative f, Alt f) => p a (f b) -> p s (f t)

type ABifocal s t a b =
  Binocular a b a (Identity b) -> Binocular a b s (Identity t)

newtype Binocular a b s t = Binocular
  { runBinocular
      :: forall f. (Applicative f, Alt f)
      => ((s -> Maybe a) -> f b) -> f t
  }
instance Tokenized a b (Binocular a b) where
  anyToken = Binocular ($ Just)
instance Profunctor (Binocular a b) where
  dimap f g (Binocular z) =
    Binocular (fmap g . z . lmap (. f))
instance Choice (Binocular a b) where
  left' = alternate . Left
  right' = alternate . Right
instance Distributor1 (Binocular a b)
instance Alternator1 (Binocular a b) where
  alternate =
    let
      lft f = either f (const Nothing)
      rght f = either (const Nothing) f
    in \case
      Left (Binocular z) ->
        Binocular (fmap Left . z . (. lft))
      Right (Binocular z) ->
        Binocular (fmap Right . z . (. rght))
instance Functor (Binocular a b s) where fmap = rmap
instance Apply (Binocular a b s) where
  (<.>) = (<*>)
  (.>) = (*>)
  (<.) = (<*)
instance Applicative (Binocular a b s) where
  pure a = Binocular $ \_ -> pure a
  Binocular f <*> Binocular a = Binocular $ \ pafb -> f pafb <*> a pafb
  liftA2 f (Binocular x) (Binocular y) = Binocular $ \pafb -> liftA2 f (x pafb) (y pafb)
  Binocular x *> Binocular y = Binocular $ \pafb -> x pafb *> y pafb
  Binocular x <* Binocular y = Binocular $ \pafb -> x pafb <* y pafb
instance Alt (Binocular a b s) where
  Binocular x <!> Binocular y = Binocular $ \ pafb -> x pafb <!> y pafb
