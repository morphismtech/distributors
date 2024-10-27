{-# LANGUAGE ImpredicativeTypes #-}

module Control.Lens.Monocle1
  ( Monocle
  , AMonocle
  , Monocular (..)
  ) where

import Control.Lens
import Control.Lens.Internal.MixedRep
import Control.Lens.Internal.Token
import Data.Bifunctor.Biff
import Data.Functor.Apply
import Data.Profunctor.Distributor1

type Monocle s t a b = forall p f.
  (Monoidal p, Applicative f) => p a (f b) -> p s (f t)

type AMonocle s t a b =
  Monocular a b a (Identity b) -> Monocular a b s (Identity t)

newtype Monocular a b s t = Monocular
  {runMonocular :: Bazaar (->) (s -> a) b t}
  deriving newtype (Functor, Apply, Applicative)
instance Tokenized a b (Monocular a b) where
  anyToken = Monocular (Bazaar ($ id))
instance Profunctor (Monocular a b) where
  dimap f g (Monocular (Bazaar z)) =
    Monocular (Bazaar (fmap g . z . lmap (. f)))

withMonocle :: AMonocle s t a b -> (Monocular a b s t -> r) -> r
withMonocle mon k =
  k (runIdentity <$> mon (Identity <$> anyToken))

cyclops :: Monoidal p => AMonocle s t a b -> p a b -> p s t
cyclops mon p = withMonocle mon
  (\(Monocular (Bazaar baz)) -> baz)
  (\sa -> lmap sa p)

-- monBitraversal
--   :: (Functor f, Applicative g, Monoidal p)
--   => AMonocle s t a b
--   -> p (f a) (g b) -> p (f s) (g t)
-- monBitraversal mon = runBiff . cyclops mon . Biff

cloneMonocle :: AMonocle s t a b -> Monocle s t a b
cloneMonocle mon = runMixedRep . cyclops mon . MixedRep
  -- = lmap Identity
  -- . monBitraversal mon
  -- . lmap runIdentity

runSpiceShop
  :: (Profunctor p, forall x. Applicative (p x))
  => Monocular a b s t
  -> ((s -> a) -> p a b)
  -> p s t
runSpiceShop (Monocular baz) f = runBazaar baz $ \sa -> lmap sa (f sa)
