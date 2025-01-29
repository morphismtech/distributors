module Data.Profunctor.Distributor
  ( Monoidal1 (..)
  , Monoidal (..)
  , Distributor1 (..)
  , Distributor (..)
  , Alternator1 (..)
  , Alternator (..)
  , Filtrator (..)
  , dimapMaybe
  , dimap2
  , dither
  , Stream
  , Stream'
  , WrappedP (..)
  , WrappedPf (..)
  , Dist (..)
  , liftDist
  ) where

import Control.Applicative
import Control.Arrow
import Control.Lens hiding ((<.>))
import Data.Functor.Alt
import Data.Profunctor
import Data.Void
import Witherable

class Profunctor p => Monoidal1 p where
  (>*<) :: p a b -> p c d -> p (a,c) (b,d)
  default (>*<)
    :: (forall x. Applicative (p x))
    => p a b -> p c d -> p (a,c) (b,d)
  x >*< y = liftA2 (,) (lmap fst x) (lmap snd y)

class Monoidal1 p => Monoidal p where
  oneP :: p () ()
  default oneP
    :: (forall x. Applicative (p x))
    => p () ()
  oneP = pure ()

class Monoidal p => Distributor1 p where

  (>+<) :: p a b -> p c d -> p (Either a c) (Either b d)
  default (>+<)
    :: Alternator1 p => p a b -> p c d -> p (Either a c) (Either b d)
  x >+< y = alternate (Left x) >|< alternate (Right y)

  optionalP :: p a b -> p (Maybe a) (Maybe b)
  optionalP p = mapIso _M2E (oneP >+< p)

  manyP :: Stream s t a b => p a b -> p s t
  manyP p = mapIso _Stream (oneP >+< many1P p)

  many1P :: Stream s t a b => p a b -> p (a,s) (b,t)
  many1P p = p >*< manyP p

class Distributor1 p => Distributor p where
  zeroP :: p Void Void
  default zeroP :: Alternator p => p Void Void
  zeroP = emptyP

class (Choice p, Distributor1 p) => Alternator1 p where

  (>|<) :: p a b -> p a b -> p a b
  default (>|<)
    :: (forall x. Alternative (p x)) => p a b -> p a b -> p a b
  (>|<) = (<|>)

  alternate :: Either (p a b) (p c d) -> p (Either a c) (Either b d)
  default alternate
    :: Cochoice p => Either (p a b) (p c d) -> p (Either a c) (Either b d)
  alternate = dimapMaybe (either Just (pure Nothing)) (Just . Left)
    ||| dimapMaybe (either (pure Nothing) Just) (Just . Right)

class (Alternator1 p, Distributor p) => Alternator p where
  emptyP :: p a b
  default emptyP :: (forall x. Alternative (p x)) => p a b
  emptyP = empty

class Cochoice p => Filtrator p where
  filtrate :: p (Either a c) (Either b d) -> (p a b, p c d)
  default filtrate
    :: Choice p => p (Either a c) (Either b d) -> (p a b, p c d)
  filtrate = dimapMaybe (Just . Left) (either Just (pure Nothing))
    &&& dimapMaybe (Just . Right) (either (pure Nothing) Just)

dimapMaybe
  :: (Choice p, Cochoice p)
  => (s -> Maybe a) -> (b -> Maybe t)
  -> p a b -> p s t
dimapMaybe f g =
  let
    m2e h = maybe (Left ()) Right . h
    fg = dimap (>>= m2e f) (>>= m2e g)
  in
    unright . fg . right'

dimap2
  :: Monoidal1 p
  => (s -> a)
  -> (s -> c)
  -> (b -> d -> t)
  -> p a b -> p c d -> p s t
dimap2 f0 f1 g x y = dimap (f0 &&& f1) (uncurry g) (x >*< y)

dither
  :: Distributor1 p
  => (s -> Either a c)
  -> (b -> t)
  -> (d -> t)
  -> p a b -> p c d -> p s t
dither f g h p q = dimap f (g ||| h) (p >+< q)

type Stream s t a b = (Cons s t a b, Stream' s a, Stream' t b)

type Stream' s a = (AsEmpty s, Cons s s a a)

_Stream
  :: Stream s t a b
  => Iso s t (Either () (a,s)) (Either () (b,t))
_Stream = _HeadTailMay . _M2E

_HeadTailMay
  :: Stream s t a b
  => Iso s t (Maybe (a,s)) (Maybe (b,t))
_HeadTailMay = iso (preview _Cons) (maybe Empty (uncurry cons))

_M2E :: Iso (Maybe a) (Maybe b) (Either () a) (Either () b)
_M2E = iso (maybe (Left ()) Right) (either (pure Nothing) Just)

mapIso :: Profunctor p => AnIso s t a b -> p a b -> p s t
mapIso i p = withIso i $ \here there -> dimap here there p

newtype WrappedP p a b = WrapP {unWrapP :: p a b}
deriving newtype instance Profunctor p => Profunctor (WrappedP p)
deriving newtype instance Choice p => Choice (WrappedP p)
deriving newtype instance Cochoice p => Cochoice (WrappedP p)
deriving newtype instance Monoidal1 p => Monoidal1 (WrappedP p)
deriving newtype instance Monoidal p => Monoidal (WrappedP p)
deriving newtype instance Distributor1 p => Distributor1 (WrappedP p)
deriving newtype instance Distributor p => Distributor (WrappedP p)
deriving newtype instance Alternator1 p => Alternator1 (WrappedP p)
deriving newtype instance Alternator p => Alternator (WrappedP p)
instance Profunctor p => Functor (WrappedP p a) where fmap = rmap
instance Monoidal1 p => Apply (WrappedP p a) where
  WrapP x <.> WrapP y =
    WrapP (dimap (\a -> (a,a)) (\(f,b) -> f b) (x >*< y))
instance Monoidal p => Applicative (WrappedP p a) where
  pure b = WrapP (dimap (\_ -> ()) (\_ -> b) oneP)
  (<*>) = (<.>)
instance Alternator1 p => Alt (WrappedP p a) where
  WrapP x <!> WrapP y = WrapP (x >|< y)
instance Alternator p => Alternative (WrappedP p a) where
  empty = WrapP emptyP
  (<|>) = (<!>)
instance Filtrator p => Filterable (WrappedP p a) where
  catMaybes (WrapP x) =
    WrapP (snd (filtrate (dimap (either absurd id) (maybe (Left ()) Right) x)))

newtype WrappedPf f p a b = WrapPf {unWrapPf :: p a (f b)}
instance (Profunctor p, Functor f) => Functor (WrappedPf f p a) where
  fmap = rmap
deriving via (WrappedP (WrappedPf f p) a)
  instance (Monoidal p, Applicative f) => Applicative (WrappedPf f p a)
instance (Profunctor p, Functor f) => Profunctor (WrappedPf f p) where
  dimap f g (WrapPf x) = WrapPf (dimap f (fmap g) x)
instance (Profunctor p, Filterable f) => Cochoice (WrappedPf f p) where
  unleft (WrapPf x) =
    WrapPf (dimap Left (catMaybes . fmap (either Just (const Nothing))) x)
  unright (WrapPf x) =
    WrapPf (dimap Right (catMaybes . fmap (either (const Nothing) Just)) x)
instance (Choice p, Applicative f) => Choice (WrappedPf f p) where
  left' (WrapPf p) =
    WrapPf (rmap (either (fmap Left) (pure . Right)) (left' p))
  right' (WrapPf p) =
    WrapPf (rmap (either (pure . Left) (fmap Right)) (right' p))
instance (Monoidal1 p, Applicative f) => Monoidal1 (WrappedPf f p) where
  WrapPf x >*< WrapPf y = WrapPf (rmap (uncurry (liftA2 (,))) (x >*< y))
instance (Monoidal p, Applicative f) => Monoidal (WrappedPf f p) where
  oneP = WrapPf (rmap pure oneP)
instance (Distributor1 p, Applicative f)
  => Distributor1 (WrappedPf f p) where
    WrapPf x >+< WrapPf y =
      WrapPf (rmap (fmap Left ||| fmap Right) (x >+< y))
instance (Distributor p, Applicative f)
  => Distributor (WrappedPf f p) where
    zeroP = WrapPf (rmap pure zeroP)
instance (Alternator1 p, Applicative f)
  => Alternator1 (WrappedPf f p) where
    WrapPf x >|< WrapPf y = WrapPf (x >|< y)
    alternate
      = WrapPf
      . rmap (either (fmap Left) (pure . Left))
      . alternate
      . Left
      . unWrapPf
      ||| WrapPf
      . rmap (either (pure . Right) (fmap Right))
      . alternate
      . Right
      . unWrapPf

data Dist p a b where
  DistVoid 
    :: (a -> Void)
    -> Dist p a b
  DistEither
    :: (a -> Either s c)
    -> p s b
    -> Dist p c b
    -> Dist p a b

liftDist :: p a b -> Dist p a b
liftDist x = DistEither Left x (DistVoid id)

instance Profunctor p => Profunctor (Dist p) where
  dimap f g = \case
    DistVoid k -> DistVoid (k . f)
    DistEither k x y -> DistEither (k . f) (rmap g x) (rmap g y)
instance Monoidal p => Monoidal1 (Dist p) where
  DistVoid k >*< _ = DistVoid (k . fst)
  DistEither k x y >*< z =
    dither (\(a,c) -> ((,c) +++ (,c)) (k a)) id id
      (liftDist x >*< z) (y >*< z)
instance Monoidal p => Monoidal (Dist p) where
  oneP = liftDist oneP
instance Monoidal p => Distributor1 (Dist p) where
  DistVoid k >+< x = dimap (absurd . k ||| id) Right x
  DistEither k x y >+< z =
    let
      assocE (Left (Left a)) = Left a
      assocE (Left (Right b)) = Right (Left b)
      assocE (Right c) = Right (Right c)
    in
      dither (assocE . (Left . k ||| Right)) Left id
        (liftDist x) (y >+< z)
instance Monoidal p => Distributor (Dist p) where
  zeroP = DistVoid id
