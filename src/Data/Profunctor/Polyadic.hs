{-|
Module      : Data.Profunctor.Polyadic
Description : polyadic & tetradic profunctors
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

{-# LANGUAGE PolyKinds, QualifiedDo #-}

module Data.Profunctor.Polyadic
  ( Polyadic (..), bindP
  , Tetradic (..)
  , TaggedP (..)
  , UntaggedT (..)
  , UntaggedC (..)
  ) where

import Control.Applicative
import Control.Category
import Control.Comonad
import Control.Lens
import Control.Monad
import Control.Monad.State
import Control.Monad.Trans.Indexed
import qualified Control.Monad.Trans.Indexed.Do as Ix
import Data.Profunctor.Monadic
import Prelude hiding (id, (.))

class
  ( forall i j. Profunctor (p i j m)
  , forall i j x. Functor (p i j m x)
  , forall i. Monadic m (p i i)
  ) => Polyadic m p where
  joinP :: p i j m a (p j k m a b) -> p i k m a b
  bondP :: (a -> p i j m b c) -> p i i m a a -> p i j m (a,b) (a,c)

bindP :: Polyadic m p => (b -> p j k m a c) -> p i j m a b -> p i k m a c
bindP f p = joinP (fmap f p)

class (forall i j. Profunctor (p i j f)) => Tetradic f p where

  tetramap
    :: (h -> i) -> (j -> k)
    -> (s -> a) -> (b -> t)
    -> p i j f a b -> p h k f s t
  tetramap f1 f2 f3 f4 = dimapT f1 f2 . dimap f3 f4

  dimapT
    :: (h -> i) -> (j -> k)
    -> p i j f a b -> p h k f a b
  dimapT f1 f2 = tetramap f1 f2 id id

newtype TaggedP t i j f a b = TagP {untagP :: t i j f b}
  deriving newtype (Functor, Applicative, Monad)
instance Functor (t i j f) => Profunctor (TaggedP t i j f) where
  dimap _ f = TagP . fmap f . untagP
instance (Monad m, IxMonadTrans t)
  => Monadic m (TaggedP t i i) where
  liftP = TagP . lift
  bondM = bondP
instance (Monad m, IxMonadTrans t)
  => Polyadic m (TaggedP t) where
  joinP = TagP . joinIx . fmap untagP . untagP
  bondP f (TagP m) = TagP $ Ix.do
    a <- m
    c <- untagP (f a)
    return (a,c)

newtype UntaggedT p a i j f b = UntagT {tagT :: p i j f a b}
  deriving newtype (Functor, Applicative, Monad)
instance (forall m. Monad m => Monadic m (p i j))
  => MonadTrans (UntaggedT p a i j) where
  lift = UntagT . liftP
instance (forall m. Monad m => Polyadic m p)
  => IxMonadTrans (UntaggedT p a) where
  joinIx = UntagT . joinP . fmap tagT . tagT

newtype UntaggedC p a b f i j = UntagC {tagC :: p i j f a b}
instance (Tetradic f p, Functor f) => Tetradic f (UntaggedC p) where
  tetramap f1 f2 f3 f4 = UntagC . tetramap f3 f4 f1 f2 . tagC
instance (Tetradic f p, Functor f) => Profunctor (UntaggedC p a b f) where
  dimap f g = UntagC . dimapT f g . tagC
instance (Tetradic f p, Functor f) => Functor (UntaggedC p a b f i) where
  fmap = rmap
instance (Polyadic m p, Monoid b) => Category (UntaggedC p a b m) where
  id = UntagC (pure mempty)
  UntagC g . UntagC f = UntagC (joinP (fmap (\b -> fmap (<> b) g) f))
instance (Polyadic m p, Monad m, Monoid b)
  => Semigroup (UntaggedC p a b m i i) where (<>) = (>>>)
instance (Polyadic m p, Monad m, Monoid b)
  => Monoid (UntaggedC p a b m i i) where mempty = id
