module Control.Applicative.Filterable
  ( fempty
  , FilterAp (..)
  , liftFilterAp
  , hoistFilterAp
  , foldFilterAp
  ) where

import Control.Monad
import Witherable

fempty
  :: (Applicative f, Filterable f)
  => f a
fempty = catMaybes (pure Nothing)

data FilterAp f a where
  FilterNil :: FilterAp f a
  FilterPure :: a -> FilterAp f a
  FilterAp
    :: FilterAp f (a -> Maybe b)
    -> f a
    -> FilterAp f b
instance Functor (FilterAp f) where
  fmap f = \case
    FilterNil -> FilterNil
    FilterPure a -> FilterPure (f a)
    FilterAp g a -> FilterAp (fmap (fmap f .) g) a
instance Applicative (FilterAp f) where
  pure = FilterPure
  FilterNil <*> _ = FilterNil
  _ <*> FilterNil = FilterNil
  FilterPure f <*> a = f <$> a
  f <*> FilterPure a = ($ a) <$> f
  FilterAp f a <*> b =
    let
      apply g c d = ($ c) <$> g d
    in
      FilterAp (apply <$> f <*> b) a
instance Filterable (FilterAp f) where
  mapMaybe f = \case
    FilterNil -> FilterNil
    FilterPure a -> maybe FilterNil FilterPure (f a)
    FilterAp g a -> FilterAp (fmap (>=> f) g) a

liftFilterAp :: f a -> FilterAp f a
liftFilterAp = FilterAp (pure Just)

hoistFilterAp :: (forall x. f x -> g x) -> FilterAp f a -> FilterAp g a
hoistFilterAp fg = \case
  FilterNil -> FilterNil
  FilterPure a -> FilterPure a
  FilterAp f a -> FilterAp (hoistFilterAp fg f) (fg a)

foldFilterAp
  :: (Applicative g, Filterable g)
  => (forall x. f x -> g x)
  -> FilterAp f a -> g a
foldFilterAp fg filtAp = catMaybes $ case filtAp of
  FilterNil -> pure Nothing
  FilterPure a -> pure (Just a)
  FilterAp f a -> ($) <$> foldFilterAp fg f <*> fg a
