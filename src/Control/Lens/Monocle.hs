{- |
Module      : Control.Lens.Monocle
Description : monocles
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Control.Lens.Monocle
  ( Monocle
  , Monocle'
  , AMonocle
  , AMonocle'
  , cloneMonocle
  , mapMonocle
  , ditraversal
  , withMonocle
  , Monocular (..), runMonocular
  , WrappedPF (..), WrappedPFG (..)
  ) where

import Control.Applicative
import Control.Lens hiding (Traversing)
-- import Control.Lens.Internal.Bazaar
-- import Control.Lens.Internal.Context
-- import Control.Lens.PartialIso
import Control.Lens.Token
import Data.Distributive
import Data.Functor.Compose
import Data.Profunctor
-- import Data.Profunctor.Traversing
import Data.Profunctor.Distributor
import Witherable

type Monocle s t a b = forall p f.
  (Monoidal p, Applicative f)
    => p a (f b) -> p s (f t)

type Monocle' s a = Monocle s s a a

type AMonocle s t a b =
  Monocular a b a (Identity b) -> Monocular a b s (Identity t)

type AMonocle' s a = AMonocle s s a a

cloneMonocle :: AMonocle s t a b -> Monocle s t a b
cloneMonocle mon = unWrapPF . mapMonocle mon . WrapPF

ditraversal
  :: (Functor f, Applicative g, Monoidal p)
  => AMonocle s t a b
  -> p (f a) (g b) -> p (f s) (g t)
ditraversal mon = unWrapPFG . mapMonocle mon . WrapPFG

mapMonocle :: Monoidal p => AMonocle s t a b -> p a b -> p s t
mapMonocle mon p =
  withMonocle mon $ \k -> runMonocular k $ \_ -> p

withMonocle :: AMonocle s t a b -> (Monocular a b s t -> r) -> r
withMonocle mon k =
  k (runIdentity <$> mon (Identity <$> anyToken))

newtype Monocular a b s t = Monocular
  {unMonocular :: forall f. Applicative f => ((s -> a) -> f b) -> f t}
instance Tokenized a b (Monocular a b) where
  anyToken = Monocular ($ id)
instance Profunctor (Monocular a b) where
  dimap f g (Monocular k) =
    Monocular (fmap g . k . (. (. f)))
instance Functor (Monocular a b s) where fmap = rmap
instance Applicative (Monocular a b s) where
  pure t = Monocular (pure (pure t))
  Monocular x <*> Monocular y = Monocular (liftA2 (<*>) x y)

runMonocular
  :: (Profunctor p, forall x. Applicative (p x))
  => Monocular a b s t
  -> ((s -> a) -> p a b)
  -> p s t
runMonocular (Monocular k) f = k $ \sa -> lmap sa (f sa)

-- newtype WrappedMonoidal p a b = WrapMonoidal
--   {unWrapMonoidal :: p a b}
-- instance Monoidal p
--   => Functor (WrappedMonoidal p a) where fmap = rmap
-- deriving newtype instance Monoidal p
--   => Applicative (WrappedMonoidal p a)
-- deriving newtype instance Monoidal p
--   => Profunctor (WrappedMonoidal p)
-- deriving newtype instance (Monoidal p, Choice p)
--   => Choice (WrappedMonoidal p)
-- deriving newtype instance (Monoidal p, Strong p)
--   => Strong (WrappedMonoidal p)
-- instance (Monoidal p, Choice p, Strong p)
--   => Traversing (WrappedMonoidal p) where
--     wander f (WrapMonoidal p) = WrapMonoidal $
--       dimap (f sell) iextract (trav p) where
--         trav :: p u v -> p (Bazaar (->) u w x) (Bazaar (->) v w x)
--         trav q = mapIso _Bazaar $ right' (q >*< trav q)

newtype WrappedPF p f a b = WrapPF {unWrapPF :: p a (f b)}
instance (Profunctor p, Functor f)
  => Functor (WrappedPF p f a) where fmap = rmap
deriving via Compose (p a) f instance
  (Monoidal p, Applicative f)
    => Applicative (WrappedPF p f a)
deriving via Compose (p a) f instance
  (Profunctor p, forall x. Alternative (p x), Applicative f)
    => Alternative (WrappedPF p f a)
deriving via Compose (p a) f instance
  (Profunctor p, forall x. Functor (p x), Filterable f)
    => Filterable (WrappedPF p f a)
instance (Profunctor p, Functor f)
  => Profunctor (WrappedPF p f) where
    dimap f g (WrapPF p) = WrapPF $ dimap f (fmap g) p
instance (Distributor p, Applicative f)
  => Distributor (WrappedPF p f) where
    zeroP = WrapPF (rmap pure zeroP)
    WrapPF x >+< WrapPF y = WrapPF $
      dialt id (fmap Left) (fmap Right) x y
    -- manyP
    -- optionalP
instance (Applicative f, Choice p)
  => Choice (WrappedPF p f) where
  left' (WrapPF p) = WrapPF $ rmap sequenceL $ left' p
    where
      sequenceL = either (fmap Left) (pure . Right)
  right' (WrapPF p) = WrapPF $ rmap sequenceL $ right' p
    where
      sequenceL = either (pure . Left) (fmap Right)
instance (Profunctor p, Filterable f)
  => Cochoice (WrappedPF p f) where
    unleft (WrapPF p) = WrapPF $
      dimap Left (mapMaybe (either Just (const Nothing))) p
    unright (WrapPF p) = WrapPF $
      dimap Right (mapMaybe (either (const Nothing) Just)) p
instance (Closed p, Distributive f)
  => Closed (WrappedPF p f) where
    closed (WrapPF p) = WrapPF (rmap distribute (closed p))
instance (Alternator p, Alternative f)
  => Alternator (WrappedPF p f) where
    alternate =
      let
        f = WrapPF
          . rmap (either (fmap Left) pure)
          . alternate
          . Left
          . unWrapPF
        g = WrapPF
          . rmap (either pure (fmap Right))
          . alternate
          . Right
          . unWrapPF
      in
        either f g
    -- someP
instance (Filtrator p, Filterable f)
  => Filtrator (WrappedPF p f) where
    filtrate (WrapPF p) =
      let
        fL = Left . mapMaybe (either Just (const Nothing))
        fR = Right . mapMaybe (either (const Nothing) Just)
        (pL,_) = filtrate (rmap fL p)
        (_,pR) = filtrate (rmap fR p)
      in
        ( WrapPF pL
        , WrapPF pR
        )

newtype WrappedPFG p f g a b = WrapPFG {unWrapPFG :: p (f a) (g b)}
instance (Profunctor p, Functor f, Functor g)
  => Functor (WrappedPFG p f g a) where fmap = rmap
deriving via Compose (p (f a)) g instance
  (Monoidal p, Functor f, Applicative g)
    => Applicative (WrappedPFG p f g a)
instance (Profunctor p, Functor f, Functor g)
  => Profunctor (WrappedPFG p f g) where
    dimap f g (WrapPFG p) = WrapPFG $ dimap (fmap f) (fmap g) p
