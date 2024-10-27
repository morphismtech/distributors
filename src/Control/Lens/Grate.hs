{-# LANGUAGE ImpredicativeTypes #-}

module Control.Lens.Grate
  ( Grate
  , AGrate
  , Grating (..)
  ) where

import Control.Lens.Internal.Token
import Data.Distributive
import Data.Functor.Identity
import Data.Functor.Rep
import Data.Profunctor
import Data.Profunctor.Distributor1

type Grate s t a b = forall p f.
  ( Closed p
  , Monoidal p
  , Distributive f
  , Applicative f
  ) => p a (f b) -> p s (f t)

type AGrate s t a b =
  Grating a b a (Identity b) -> Grating a b s (Identity t)

newtype Grating a b s t = Grating {unGrating :: ((s -> a) -> b) -> t}
instance Functor (Grating a b s) where fmap = rmap
instance Applicative (Grating a b s) where
  pure = pureRep
  (<*>) = apRep
instance Distributive (Grating a b s) where
  collect = collectRep
  distribute = distributeRep
instance Representable (Grating a b s) where
  type Rep (Grating a b s) = (s -> a) -> b
  index (Grating d) r = d r
  tabulate = Grating
instance Profunctor (Grating a b) where
  dimap f g (Grating z) = Grating $ \d ->
    g . z $ \k -> d (k . f)
instance Closed (Grating a b) where
  closed (Grating z) = Grating $ \f x ->
    z $ \k -> f $ \g -> k (g x)
instance Tokenized a b (Grating a b) where
  anyToken = Grating ($ id)
