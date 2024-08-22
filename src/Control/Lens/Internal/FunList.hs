module Control.Lens.Internal.FunList
  ( FunList (..)
  , _FunList
  , _Bazaar
  , Shop (..)
  , shop
  , runShop
  , Purchase (..)
  , buy
  , Peano (..)
  , V (..)
  , SomeV (..)
  , N
  , Ns
  ) where

import Control.Lens
import Control.Lens.Internal.Bazaar
import Control.Lens.Internal.Context
import GHC.TypeNats

{- | `FunList` is isomorphic to `Bazaar` @(->)@,
but modified so its nil and cons are pattern matchable.
`FunList` is isomorphic to some homogeneous tuple
of one type paired with a function from that tuple,
of another type.

prop> FunList a b t ~ Bazaar (->) a b t
prop> FunList a b t ~ exists (..) :: Natural. ((a,..,a), b -> .. -> b -> t)
prop> FunList a b t ~ exists (..) :: Natural. ((a,..,a), (b,..,b) -> t)
-}
data FunList a b t
  = DoneFun t
  | MoreFun (Bazaar (->) a b (b -> t)) a
instance Functor (FunList a b) where
  fmap f = \case
    DoneFun t -> DoneFun (f t)
    MoreFun h a -> MoreFun (fmap (f .) h) a
instance Applicative (FunList a b) where
  pure = DoneFun
  (<*>) = \case
    DoneFun t -> fmap t
    MoreFun h a -> \l ->
      MoreFun (flip <$> h <*> review _FunList l) a
instance Sellable (->) FunList where sell = MoreFun (pure id)
instance Bizarre (->) FunList where
  bazaar f = \case
    DoneFun t -> pure t
    MoreFun l a -> ($) <$> bazaar f l <*> f a
_FunList :: Iso
  (Bazaar (->) a1 b1 t1) (Bazaar (->) a2 b2 t2)
  (FunList a1 b1 t1) (FunList a2 b2 t2)
_FunList = iso toFun fromFun where
  toFun (Bazaar f) = f sell
  fromFun = \case
    DoneFun t -> pure t
    MoreFun f a -> ($) <$> f <*> sell a

_Bazaar :: Iso
  (Bazaar (->) a1 b1 t1) (Bazaar (->) a2 b2 t2)
  (Either t1 (Bazaar (->) a1 b1 (b1 -> t1), a1))
  (Either t2 (Bazaar (->) a2 b2 (b2 -> t2), a2))
_Bazaar = _FunList . dimap f (fmap g) where
  f = \case
    DoneFun t -> Left t
    MoreFun baz a -> Right (baz, a)
  g = \case
    Left t -> DoneFun t
    Right (baz, a) -> MoreFun baz a

{- | A `Shop` is a fixed length homogeneous tuple isomorphism.

prop> Shop a b s t ~ Bazaar (->) (s -> a) b t
prop> Shop a b s t ~ FunList (s -> a) b t
prop> Shop a b s t ~ exists (..) :: Natural. ((s -> a,..,s -> a), b -> .. -> b -> t)
prop> Shop a b s t ~ exists (..) :: Natural. (s -> (a,..,a), (b,..,b) -> t)
-}
newtype Shop a b s t = Shop
  {unShop :: Bazaar (->) (s -> a) b t}
  deriving newtype (Functor, Applicative)
instance Profunctor (Shop a b) where
  dimap f g (Shop baz) = Shop . review _FunList $
    case view _FunList baz of
      DoneFun c -> DoneFun (g c)
      MoreFun baz' h ->
        MoreFun (unShop (dimap f (g .) (Shop baz'))) (h . f)
runShop
  :: (Profunctor p, forall x. Applicative (p x))
  => Shop a b s t
  -> ((s -> a) -> p a b)
  -> p s t
runShop (Shop baz) f = runBazaar baz $ \sa -> lmap sa (f sa)
shop :: Shop a b a b
shop = Shop (sell id)

{- | An indexed continuation monad -}
newtype Purchase a b s = Purchase {unPurchase :: (s -> a) -> b}
instance Functor (Purchase a b) where
  fmap sl (Purchase ab) = Purchase $ \la -> ab (la . sl)
instance a ~ b => Applicative (Purchase a b) where
  pure s = Purchase ($ s)
  Purchase slab <*> Purchase ab =
    Purchase $ \la -> slab $ \sl -> ab (la . sl)
buy :: Purchase a b a -> b
buy (Purchase f) = f id

-- Peano datatypes
data Peano = Z | S Peano

data V (n :: Peano) x where
  VNil :: V Z x
  (:><) :: x -> V n x -> V (S n) x
instance Functor (V n) where
  fmap f = \case
    VNil -> VNil
    x :>< y -> f x :>< fmap f y

data SomeV (ns :: [Peano]) x where
  VFst :: V n x -> SomeV (n ': ns) x
  VNxt :: SomeV ns x -> SomeV (n ': ns) x
instance Functor (SomeV ns) where
  fmap f = \case
    VFst v -> VFst (fmap f v)
    VNxt s -> VNxt (fmap f s)

type family N (n :: Natural) where
  N 0 = Z
  N n = S (N (n - 1))

type family Ns (ns :: [Natural]) where
  Ns '[] = '[]
  Ns (n ': ns) = N n ': Ns ns
