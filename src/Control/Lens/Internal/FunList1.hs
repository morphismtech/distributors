module Control.Lens.Internal.FunList1
  ( funList
  , FunList (..)
  , funListBazaar
  ) where

import Control.Lens
import Control.Lens.Internal.Bazaar
import Control.Lens.Internal.Context

funList :: Iso
  (Bazaar (->) a1 b1 t1) (Bazaar (->) a2 b2 t2)
  (Either t1 (a1, Bazaar (->) a1 b1 (b1 -> t1)))
  (Either t2 (a2, Bazaar (->) a2 b2 (b2 -> t2)))
funList =
  funListBazaar . iso unFunList FunList

newtype FunList a b t = FunList
  {unFunList :: Either t (a, Bazaar (->) a b (b -> t))}
instance Functor (FunList a b) where
  fmap f = \case
    FunList (Left t) -> FunList (Left (f t))
    FunList (Right (a, h)) -> FunList (Right (a, fmap (f .) h))
instance Applicative (FunList a b) where
  pure = FunList . Left
  (<*>) = \case
    FunList (Left t) -> fmap t
    FunList (Right (a,h)) -> \l -> FunList $
      Right (a, flip <$> h <*> review funListBazaar l)
instance Sellable (->) FunList where
  sell b = FunList (Right (b, pure id))
instance Bizarre (->) FunList where
  bazaar f = \case
    FunList (Left t) -> pure t
    FunList (Right (a,l)) -> ($) <$> bazaar f l <*> f a

funListBazaar :: Iso
  (Bazaar (->) a1 b1 t1) (Bazaar (->) a2 b2 t2)
  (FunList a1 b1 t1) (FunList a2 b2 t2)
funListBazaar = iso
  (\(Bazaar f) -> f sell)
  (either pure (\(a,f) -> ($) <$> f <*> sell a) . unFunList)
