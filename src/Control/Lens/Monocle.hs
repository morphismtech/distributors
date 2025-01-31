{- |
Module      : Control.Lens.Monocle
Description : monocles
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Control.Lens.Monocle
  ( Monocle
  , Monocle'
  , AMonocle
  , AMonocle'
  , cloneMonocle
  , mapMonocle
  , meander
  , ditraversal
  , withMonocle
  , Monocular (..), runMonocular
  , WrappedPF (..), WrappedPFG (..)
  ) where

import Control.Lens hiding (Traversing)
import Control.Lens.Internal.Bazaar
import Control.Lens.Internal.Context
import Control.Lens.Internal.Distributor
import Control.Lens.PartialIso
import Control.Lens.Token
import Data.Profunctor
import Data.Profunctor.Distributor

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

meander
  :: forall p s t a b. (Monoidal p, Choice p, Strong p)
  => ATraversal s t a b -> p a b -> p s t
meander f p = dimap (f sell) iextract (trav p)
  where
    trav :: p u v -> p (Bazaar (->) u w x) (Bazaar (->) v w x)
    trav q = mapIso _Bazaar $ right' (q >*< trav q)

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

data FunList a b t
  = DoneFun t
  | MoreFun a (Bazaar (->) a b (b -> t))
instance Functor (FunList a b) where
  fmap f = \case
    DoneFun t -> DoneFun (f t)
    MoreFun a h -> MoreFun a (fmap (f .) h)
instance Applicative (FunList a b) where
  pure = DoneFun
  (<*>) = \case
    DoneFun t -> fmap t
    MoreFun a h -> \l ->
      MoreFun a (flip <$> h <*> view _FunList l)
instance Sellable (->) FunList where sell b = MoreFun b (pure id)
instance Bizarre (->) FunList where
  bazaar f = \case
    DoneFun t -> pure t
    MoreFun a l -> ($) <$> bazaar f l <*> f a

_FunList :: Iso
  (FunList a1 b1 t1) (FunList a2 b2 t2)
  (Bazaar (->) a1 b1 t1) (Bazaar (->) a2 b2 t2)
_FunList = iso fromFun toFun where
  toFun (Bazaar f) = f sell
  fromFun = \case
    DoneFun t -> pure t
    MoreFun a f -> ($) <$> f <*> sell a

_Bazaar :: Iso
  (Bazaar (->) a1 b1 t1) (Bazaar (->) a2 b2 t2)
  (Either t1 (a1, Bazaar (->) a1 b1 (b1 -> t1)))
  (Either t2 (a2, Bazaar (->) a2 b2 (b2 -> t2)))
_Bazaar = from _FunList . iso f g where
  f = \case
    DoneFun t -> Left t
    MoreFun a baz -> Right (a, baz)
  g = \case
    Left t -> DoneFun t
    Right (a, baz) -> MoreFun a baz

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
