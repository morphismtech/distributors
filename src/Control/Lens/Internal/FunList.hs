module Control.Lens.Internal.FunList
  ( FunList (..)
  , _FunList
  , _Bazaar
  , FunV (..)
  , _FunV
  , FunSomeV (..)
  , Shop (..)
  , runShop
  , Grating (..)
  , Peano (..)
  , V (..)
  , SomeV (..)
  , N
  , Ns
  , Zabar (..)
  , Posh (..)
  , runPosh
  , Pafb (..)
  , Tokenized (..)
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.Internal.Iso
import Control.Lens.Internal.Bazaar
import Control.Lens.Internal.Context
import Control.Lens.Internal.Prism
import Data.Functor.Compose
import Data.Functor.Rep
import Data.Distributive
import Data.Profunctor
import Data.Profunctor.Partial
import Data.Profunctor.Rep hiding (Representable (..))
import qualified Data.Profunctor.Rep as Pro
import Data.Profunctor.Sieve
import GHC.TypeNats
import Prelude hiding (filter)
import Witherable

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

newtype Zabar p a b t = Zabar
  { runZabar
      :: forall f. (Filterable f, Alternative f)
      => p a (f b) -> f t
  }
instance Functor (Zabar p a b) where
  fmap f (Zabar k) = Zabar (fmap f . k)
instance Applicative (Zabar p a b) where
  pure a = Zabar $ \_ -> pure a
  Zabar mf <*> Zabar ma = Zabar $ \ pafb -> mf pafb <*> ma pafb
instance Alternative (Zabar p a b) where
  empty = Zabar $ \_ -> empty
  Zabar mx <|> Zabar my = Zabar $ \ pafb -> mx pafb <|> my pafb
instance Filterable (Zabar p a b) where
  mapMaybe f (Zabar k) = Zabar (mapMaybe f . k)
  catMaybes (Zabar k) = Zabar $ \ pafb -> catMaybes (k pafb)
  filter f (Zabar k) = Zabar (filter f . k)
instance Corepresentable p => Sellable p (Zabar p) where
  sell
    = cotabulate
    $ \w -> Zabar
    $ Pro.tabulate
    $ \k -> pure (cosieve k w)

newtype Posh a b s t = Posh
  {unPosh :: Zabar (->) (s -> Maybe a) b t}
  deriving newtype (Functor, Applicative, Alternative, Filterable)
instance Profunctor (Posh a b) where
  dimap f g (Posh (Zabar k))
    = Posh $ Zabar $ fmap g . k . (. (. f))
instance Cochoice (Posh a b) where
  unleft (Posh (Zabar k))
    = Posh $ Zabar $ catMaybes
    . fmap (either Just (const Nothing))
    . k . (. (. Left))
  unright (Posh (Zabar k))
    = Posh $ Zabar $ catMaybes
    . fmap (either (const Nothing) Just)
    . k . (. (. Right))
instance Choice (Posh a b) where
  left' (Posh (Zabar k))
    = Posh $ Zabar $ fmap Left
    . k . (. (\f -> either f (const Nothing)))
  right' (Posh (Zabar k))
    = Posh $ Zabar $ fmap Right
    . k . (. (\f -> either (const Nothing) f))

runPosh
  :: ( Choice p
     , Cochoice p
     , forall x. Alternative (p x)
     , forall x. Filterable (p x)
     )
  => Posh a b s t
  -> ((s -> Maybe a) -> p a b)
  -> p s t
runPosh (Posh zab) f = runZabar zab $ \sa -> dimapMaybe sa Just (f sa)

posh :: Posh a b a b
posh = Posh (sell Just)


newtype Pafb f p a b = Pafb {runPafb :: p a (f b)}
instance
  ( Functor f
  , Profunctor p
  ) => Functor (Pafb f p a) where fmap = rmap
instance
  ( Functor f
  , Profunctor p
  ) => Profunctor (Pafb f p) where
    dimap f g (Pafb p) = Pafb (dimap f (fmap g) p)
deriving via (Compose (p a) f) instance
  ( Applicative f
  , forall x. Applicative (p x)
  , Profunctor p
  ) => Applicative (Pafb f p a)
instance
  ( Filterable f
  , Profunctor p
  ) => Filterable (Pafb f p a) where
    catMaybes (Pafb p) = Pafb (rmap catMaybes p)
    mapMaybe f (Pafb p) = Pafb (rmap (mapMaybe f) p)
instance
  ( Filterable f
  , Profunctor p
  ) => Cochoice (Pafb f p) where
    unleft (Pafb p) = Pafb $
      dimap Left (mapMaybe (either Just (const Nothing))) p
    unright (Pafb p) = Pafb $
      dimap Right (mapMaybe (either (const Nothing) Just)) p
instance
  ( Applicative f
  , Choice p
  ) => Choice (Pafb f p) where
  left' (Pafb p) = Pafb $
    rmap (either (fmap Left) (pure . Right)) (left' p)
deriving via (Compose (p a) f) instance
  ( Applicative f
  , forall x. Alternative (p x)
  , Profunctor p
  ) => Alternative (Pafb f p a)
instance
  ( Distributive f
  , Closed p
  ) => Closed (Pafb f p) where
    closed (Pafb p) = Pafb (rmap distribute (closed p))

class Tokenized a b p | p -> a, p -> b where
  anyToken :: p a b
instance Tokenized a b (Identical a b) where
  anyToken = Identical
instance Tokenized a b (Shop a b) where
  anyToken = shop
instance Tokenized a b (Posh a b) where
  anyToken = posh
instance Tokenized a b (Grating a b) where
  anyToken = grating
instance Tokenized a b (Exchange a b) where
  anyToken = Exchange id id
instance Tokenized a b (Market a b) where
  anyToken = Market id Right
