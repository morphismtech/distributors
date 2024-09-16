module Control.Lens.Internal.FunList
  ( FunList (..)
  , _FunList
  , _Bazaar
  , FunV (..)
  , _FunV
  , FunSomeV (..)
  , Shop (..)
  , shop
  , runShop
  , Grating (..)
  , grating
  , Peano (..)
  , V (..)
  , SomeV (..)
  , N
  , Ns
  ) where

import Control.Lens
import Control.Lens.Internal.Bazaar
import Control.Lens.Internal.Context
import Data.Functor.Rep
import Data.Distributive
import Data.Profunctor.Closed
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

data FunV a b t = forall n. FunV (V n a) (V n b -> t)
_FunV :: Iso
  (FunV a0 b0 t0) (FunV a1 b1 t1)
  (FunList a0 b0 t0) (FunList a1 b1 t1)
_FunV = iso fromFunV toFunV where
  fromFunV :: FunV a b t -> FunList a b t
  fromFunV (FunV as f) = case as of
    VNil -> DoneFun (f VNil)
    a :>< v -> MoreFun a
      $ view _FunList
      . fromFunV
      . FunV v
      $ \bs b -> f (b :>< bs)
  toFunV :: FunList a b t -> FunV a b t
  toFunV = \case
    DoneFun t -> FunV VNil (pure t)
    MoreFun a baz -> case toFunV (review _FunList baz) of
      FunV as f -> FunV (a :>< as) (\(b :>< bs) -> f bs b)

data FunSomeV a b t =
  forall ns. FunSomeV (SomeV ns a) (SomeV ns b -> t)

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
  dimap f g (Shop baz) = Shop . view _FunList $
    case review _FunList baz of
      DoneFun c -> DoneFun (g c)
      MoreFun h baz' ->
        MoreFun (h . f) (unShop (dimap f (g .) (Shop baz')))

runShop
  :: (Profunctor p, forall x. Applicative (p x))
  => Shop a b s t
  -> ((s -> a) -> p a b)
  -> p s t
runShop (Shop baz) f = runBazaar baz $ \sa -> lmap sa (f sa)

shop :: Shop a b a b
shop = Shop (sell id)

newtype Grating a b s t = Grating {unGrating :: ((s -> a) -> b) -> t}
instance Functor (Grating a b s) where
  fmap = rmap
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

grating :: Grating a b a b
grating = Grating ($ id)

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
