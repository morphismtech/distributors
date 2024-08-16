{- |
Module      :  Control.Lens.Monocle
Description :  monocles
Copyright   :  (C) 2024 - Eitan Chatav
License     :  BSD-style (see the file LICENSE)
Maintainer  :  Eitan Chatav <eitan.chatav@gmail.com>
Stability   :  provisional
Portability :  non-portable

`Monocle`s are optics that combine `Control.Lens.Traversal`s and
cotraversals, also known as grates.
-}
module Control.Lens.Monocle
  ( Monocle
  , AMonocle
  , withMonocle
  , (>..<)
  , monBitraversal
  , cloneMonocle
  , monTraversal
  , monCotraversal
  , monGrate
  , monocle0
  , monocle2
    -- * Internal
  , Shop (..)
  , shop
  , runShop
  , Purchase (..)
  , buy
  ) where

import Control.Lens hiding (index, Traversing)
import Control.Lens.Internal.Context
import Data.Bifunctor.Biff
import Data.Profunctor
import Data.Profunctor.Monoidal

{- | A `Monocle` is a fixed length homogeneous tuple isomorphism.

prop> Monocle s t a b ~ (s -> (a,..,a), (b,..,b) -> t)

`Monocle` is part of a subtyping order:

prop> Iso s t a b < Monocle s t a b < Traversal s t a b

`Monocle`s may be used as cotraversals or equivalently, grates.
-}
type Monocle s t a b = forall p f.
  (Monoidal p, Applicative f) => p a (f b) -> p s (f t)

type AMonocle s t a b =
  Shop a b a (Identity b) -> Shop a b s (Identity t)

withMonocle :: AMonocle s t a b -> (Shop a b s t -> r) -> r
withMonocle mon k =
  k (runIdentity <$> mon (Identity <$> shop))

(>..<) :: Monoidal p => AMonocle s t a b -> p a b -> p s t
mon >..< p = withMonocle mon (\sh -> runShop sh (\_ -> p))

monBitraversal
  :: (Functor f, Applicative g, Monoidal p)
  => AMonocle s t a b
  -> p (f a) (g b) -> p (f s) (g t)
monBitraversal mon = runBiff . (mon >..<) . Biff

cloneMonocle :: AMonocle s t a b -> Monocle s t a b
cloneMonocle mon
  = lmap Identity
  . monBitraversal mon
  . lmap runIdentity

monTraversal :: AMonocle s t a b -> Traversal s t a b
monTraversal = cloneMonocle

monCotraversal
  :: (Functor f, Monoidal p)
  => AMonocle s t a b -> p (f a) b -> p (f s) t
monCotraversal mon
  = rmap runIdentity
  . monBitraversal mon
  . rmap Identity

monGrate :: Closed p => AMonocle s t a b -> p a b -> p s t
monGrate mon = dimap (&) (monCotraversal mon buy . Purchase) . closed

monocle0 :: Monocle () () a b
monocle0 _ = pureP (pure ())

monocle2 :: Monocle (a,a) (b,b) a b
monocle2 p = dimap2 fst snd (liftA2 (,)) p p

newtype Shop a b s t = Shop
  {unShop :: Bazaar (->) (s -> a) b t}
  deriving newtype (Functor, Applicative)
instance Profunctor (Shop a b) where
  dimap f g (Shop baz) = Shop . review _FunList $
    case view _FunList baz of
      FunPure c -> FunPure (g c)
      FunAp baz' h ->
        FunAp (unShop (dimap f (g .) (Shop baz'))) (h . f)
instance Monoidal (Shop a b)

runShop
  :: Monoidal p
  => Shop a b s t
  -> ((s -> a) -> p a b)
  -> p s t
runShop (Shop baz) f =
  unWrapMonoidal . runBazaar baz $ \sa ->
    lmap sa (WrapMonoidal (f sa))

shop :: Shop a b a b
shop = Shop (sell id)

-- An indexed continuation monad
newtype Purchase a b s = Purchase {unPurchase :: (s -> a) -> b}

instance Functor (Purchase a b) where
  fmap sl (Purchase ab) = Purchase $ \la -> ab (la . sl)

instance a ~ b => Applicative (Purchase a b) where
  pure s = Purchase ($ s)
  Purchase slab <*> Purchase ab =
    Purchase $ \la -> slab $ \sl -> ab (la . sl)

buy :: Purchase a b a -> b
buy (Purchase f) = f id
