{-# LANGUAGE ImpredicativeTypes #-}

module Control.Lens.Tint
  ( Tint
  , ATint
  , Tinting (..)
  ) where

import Control.Applicative
import qualified Control.Applicative as Alt0 (many, some)
import Control.Lens.Internal.Token
import Data.Functor.Apply
import Data.Functor.Alt
import Data.Profunctor
import Data.Profunctor.Distributor1
import Data.Profunctor.Partial1
import Witherable

type Tint s t a b = forall p f.
  (Alternator p, Cochoice p, Alternative f, Filterable f)
    => p a (f b) -> p s (f t)

type ATint s t a b =
  Tinting a b a (Maybe b) -> Tinting a b s (Maybe t)

newtype Tinting a b s t = Tinting
  { runTinting
      :: forall f. (Alternative f, Filterable f)
      => ((s -> Maybe a) -> f b) -> f t
  }
instance Tokenized a b (Tinting a b) where
  anyToken = Tinting ($ Just)
instance Profunctor (Tinting a b) where
  dimap f g (Tinting z) =
    Tinting (fmap g . z . lmap (. f))
instance Cochoice (Tinting a b) where
  unleft (Tinting k)
    = Tinting $ catMaybes
    . fmap (either Just (const Nothing))
    . k . (. (. Left))
  unright (Tinting k)
    = Tinting $ catMaybes
    . fmap (either (const Nothing) Just)
    . k . (. (. Right))
instance Choice (Tinting a b) where
  left' = alternate . Left
  right' = alternate . Right
instance Distributor1 (Tinting a b)
instance Distributor (Tinting a b)
instance Alternator1 (Tinting a b) where
  alternate =
    let
      lft f = either f (const Nothing)
      rght f = either (const Nothing) f
    in \case
      Left (Tinting z) ->
        Tinting (fmap Left . z . (. lft))
      Right (Tinting z) ->
        Tinting (fmap Right . z . (. rght))
instance Functor (Tinting a b s) where fmap = rmap
instance Apply (Tinting a b s) where
  (<.>) = (<*>)
  (.>) = (*>)
  (<.) = (<*)
instance Applicative (Tinting a b s) where
  pure a = Tinting $ \_ -> pure a
  Tinting f <*> Tinting a = Tinting $ \ pafb -> f pafb <*> a pafb
  liftA2 f (Tinting x) (Tinting y) = Tinting $ \pafb -> liftA2 f (x pafb) (y pafb)
  Tinting x *> Tinting y = Tinting $ \pafb -> x pafb *> y pafb
  Tinting x <* Tinting y = Tinting $ \pafb -> x pafb <* y pafb
instance Alt (Tinting a b s) where
  (<!>) = (<|>)
  many = Alt0.many
  some = Alt0.some
instance Alternative (Tinting a b s) where
  empty = Tinting $ \_ -> empty
  Tinting x <|> Tinting y = Tinting $ \ pafb -> x pafb <|> y pafb
  many (Tinting x) = Tinting (Alt0.many . x)
  some (Tinting x) = Tinting (Alt0.some . x)
instance Filterable (Tinting a b s) where
  mapMaybe = dimapMaybe Just
