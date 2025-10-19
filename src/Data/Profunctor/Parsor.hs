module Data.Profunctor.Parsor
  ( -- *
    Parsor (..)
  , Printor (..)
  , PP (..)
--   , toParsor
--   , toPrintor
--   , pp
--   , Separator (..)
--   , SepBy (..)
--   , Stream1 (..)
--   , Stream (..)
--   , Tokenized (..)
--   , satisfy
--   , Categorized (..)
  ) where

import Control.Applicative
import Control.Category
import Control.Monad
import Data.Bifunctor
import Data.Coerce
import Data.Profunctor
import Prelude hiding ((.), id)

newtype Parsor s t f a b = Parsor {runParsor :: s -> f (b,t)}

instance Functor f => Functor (Parsor s t f a) where
  fmap f = Parsor . (fmap (first' f) .) . runParsor
instance Functor f => Bifunctor (Parsor s t f) where
  bimap _ = (>>>) coerce . fmap
  first _ = coerce
  second = fmap
instance Functor f => Profunctor (Parsor s t f) where
  dimap _ = (<<<) coerce . fmap
  lmap _ = coerce
  rmap = fmap

instance Monad m => Applicative (Parsor s s m a) where
  pure b = Parsor (\s -> return (b,s))
  Parsor x <*> Parsor y = Parsor $ \s -> do
    (f, t) <- x s
    (a, u) <- y t
    return (f a, u)
instance Monad m => Monad (Parsor s s m a) where
  Parsor p >>= f = Parsor $ \s -> do
    (a, t) <- p s
    runParsor (f a) t
instance (Alternative m, Monad m) => Alternative (Parsor s s m a) where
  empty = Parsor (\_ -> empty)
  Parsor p <|> Parsor q = Parsor (\str -> p str <|> q str)
instance (Alternative m, Monad m) => MonadPlus (Parsor s s m a)

newtype Printor s t f a b = Printor {runPrintor :: a -> f (s -> t)}

newtype PP s t f a b = PP {runPP :: a -> s -> f (b, s -> t)}

-- toParsor :: Functor f => PP a b f s t -> Parsor s t f a b -- s -> a -> f (t, s -> b)
-- toPrintor :: Functor f => PP s t f a b -> Printor s t f a b
-- pp :: Applicative f => Parsor s t f a b -> Printor s t f a b -> PP s t f a b
