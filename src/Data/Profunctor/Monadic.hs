{-|
Module      : Data.Profunctor.Monadic
Description : distributors
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Data.Profunctor.Monadic
  ( Monadic
  , return
  , (>>=)
  , (>>)
  , Lintor (..), toPrintor, fromPrintor
  ) where

import Control.Applicative
import Control.Arrow
import Control.Category
import Control.Lens.Cons
import Control.Monad hiding ((>>), (>>=))
import Data.Profunctor
import Data.Profunctor.Distributor
import Data.String
import Data.Void
import qualified Prelude as P ((>>), (>>=))
import Prelude hiding ((>>), (>>=), id, (.))
import Witherable

type Monadic p = (Profunctor p, forall x. Monad (p x))

(>>) :: Monadic p => p () c -> p a b -> p a b
x >> y = lmap (const ()) x P.>> y

(>>=) :: Monadic p => p a a -> (a -> p a a) -> p a a
(>>=) = (P.>>=)

newtype Lintor s f a b = Lintor {runLintor :: a -> f (b, s -> s)}
instance Functor f => Functor (Lintor s f a) where fmap = rmap
instance Applicative f => Applicative (Lintor s f a) where
  pure b = Lintor (\_ -> pure (b, id))
  Lintor f <*> Lintor x = Lintor $ \c ->
    liftA2 (\(g, p) (a, q) -> (g a, p . q)) (f c) (x c)
instance Alternative f => Alternative (Lintor s f a) where
  empty = Lintor (\_ -> empty)
  Lintor p <|> Lintor q = Lintor (\a -> p a <|> q a)
instance Filterable f => Filterable (Lintor s f a) where
  mapMaybe f (Lintor p) = Lintor $
    mapMaybe (\(a,q) -> fmap (, q) (f a)) . p
instance Monad f => Monad (Lintor s f a) where
  return = pure
  Lintor x >>= f = Lintor $ \a -> do
    (c, p) <- x a
    (b, q) <- runLintor (f c) a
    return (b, p . q)
instance (Alternative f, Monad f) => MonadPlus (Lintor s f a)
instance Functor f => Profunctor (Lintor s f) where
  dimap f g (Lintor h) = Lintor (fmap (first' g) . h . f)
instance Applicative f => Distributor (Lintor s f) where
  zeroP = Lintor absurd
  Lintor p >+< Lintor q = Lintor $
    either (fmap (first' Left) . p) (fmap (first' Right) . q)
instance Alternative f => Alternator (Lintor s f) where
  alternate = \case
    Left (Lintor p) -> Lintor $
      either (fmap (first' Left) . p) (\_ -> empty)
    Right (Lintor p) -> Lintor $
      either (\_ -> empty) (fmap (first' Right) . p)
instance Filterable f => Filtrator (Lintor s f) where
  filtrate (Lintor p) =
    ( Lintor (mapMaybe (\case{(Left b, q) -> Just (b, q); _ -> Nothing}) . p . Left)
    , Lintor (mapMaybe (\case{(Right b, q) -> Just (b, q); _ -> Nothing}) . p . Right)
    )
instance Alternative f => Choice (Lintor s f) where
  left' = alternate . Left
  right' = alternate . Right
instance Filterable f => Cochoice (Lintor s f) where
  unleft = fst . filtrate
  unright = snd . filtrate
instance (Applicative f, Cons s t a b, s ~ t, a ~ b)
  => Tokenized a b (Lintor s f) where
    anyToken = Lintor (\b -> pure (b, cons b))
instance (Applicative f, Filterable f, Cons s s Char Char, a ~ (), b ~ ())
  => IsString (Lintor s f a b) where
    fromString = tokens
instance Functor f => Strong (Lintor s f) where
  first' (Lintor p) = Lintor (\(a,c) -> fmap (\(b,q) -> ((b,c),q)) (p a))
  second' (Lintor p) = Lintor (\(c,a) -> fmap (\(b,q) -> ((c,b),q)) (p a))
instance Monad f => Category (Lintor s f) where
  id = Lintor $ \a -> return (a, id)
  Lintor q . Lintor p = Lintor $ \a -> do
    (b, p') <- p a
    (c, q') <- q b
    return (c, q' . p')
instance Monad f => Arrow (Lintor s f) where
  arr f = Lintor (return . (, id) . f)
  (***) = (>*<)
  first = first'
  second = second'

toPrintor :: Functor f => Lintor s f a b -> Printor s f a b
toPrintor (Lintor p) = Printor (fmap snd . p)

fromPrintor :: Functor f => Printor s f a a -> Lintor s f a a
fromPrintor (Printor p) = Lintor (\a -> fmap (a,) (p a))
