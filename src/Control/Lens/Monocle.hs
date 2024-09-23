{- |
Module      :  Control.Lens.Monocle
Description :  monocles
Copyright   :  (C) 2024 - Eitan Chatav
License     :  BSD-style (see the file LICENSE)
Maintainer  :  Eitan Chatav <eitan.chatav@gmail.com>
Stability   :  provisional
Portability :  non-portable

`Monocle`s are optics that combine
`Control.Lens.Traversal.Traversal`s and
cotraversals, also known as grates.
-}
module Control.Lens.Monocle
  ( -- * Monocle types
    Monocle
  , AMonocle
  , Monocle'
  , AMonocle'
    -- * Monocle functions
  , withMonocle
  , monocle
  , monocle0
  , monocle2
  , MonocleN (..)
  , cyclops
  , cloneMonocle
  , monTraversal
  , monGrate
  , monBitraversal
  , Grate
  , Grate'
  , AGrate
  , AGrate'
  , grate
  , withGrate
  , cloneGrate
  , cotraversed
  , represented
  , closing
  , distributing
  , cotraverseOf
  , collectOf
  , distributeOf
  ) where

import Control.Lens hiding (index, Traversing)
import Control.Lens.Internal.FunList
import Data.Bifunctor.Biff
import Data.Distributive
import Data.Functor.Rep
import Data.Profunctor
import Data.Profunctor.Monoidal

{- | A `Monocle` is a representation of a
fixed length homogeneous tuple dimorphism.

prop> Monocle s t a b ~ exists (..) :: Natural. (s -> (a,..,a), (b,..,b) -> t)

`Monocle` is part of a subtyping order:

prop> Iso s t a b < Monocle s t a b < Traversal s t a b

`Monocle`s may be used as cotraversals or equivalently, grates.
-}
type Monocle s t a b = forall p f.
  (Monoidal p, Applicative f) => p a (f b) -> p s (f t)

{- | `Simple` `Monocle`. -}
type Monocle' s a = Monocle s s a a

{- | If you see this in a signature for a function,
the function is expecting a `Monocle`. -}
type AMonocle s t a b =
  SpiceShop a b a (Identity b) -> SpiceShop a b s (Identity t)

{- | A `Simple` `Monocle`. -}
type AMonocle' s a = AMonocle s s a a

{- | Turn a `AMonocle` into a curried homogeneous tuple dimorphism. -}
withMonocle :: AMonocle s t a b -> (SpiceShop a b s t -> r) -> r
withMonocle mon k =
  k (runIdentity <$> mon (Identity <$> anyToken))

{- | Turn  a curried homogeneous tuple dimorphism into a `Monocle`.-}
monocle :: SpiceShop a b s t -> Monocle s t a b
monocle sh =
  cloneMonocle $ \p ->
    unWrapMonoidal $
      runSpiceShop (Identity <$> sh) $ \_ ->
        WrapMonoidal $ runIdentity <$> p

{- | The natural action of `AMonocle` on `Monoidal`. -}
cyclops :: Monoidal p => AMonocle s t a b -> p a b -> p s t
cyclops mon p =
  withMonocle mon $ \sh ->
    unWrapMonoidal . runSpiceShop sh $ \_ ->
      WrapMonoidal p

{- | `AMonocle` as a `Bitraversal`. -}
monBitraversal
  :: (Functor f, Applicative g, Monoidal p)
  => AMonocle s t a b
  -> p (f a) (g b) -> p (f s) (g t)
monBitraversal mon = runBiff . cyclops mon . Biff

{- | Clone `AMonocle` as a `Monocle`. -}
cloneMonocle :: AMonocle s t a b -> Monocle s t a b
cloneMonocle mon
  = lmap Identity
  . monBitraversal mon
  . lmap runIdentity

{- | `AMonocle` as a `Control.Lens.Traversal.Traversal`. -}
monTraversal :: AMonocle s t a b -> Traversal s t a b
monTraversal = cloneMonocle

{- | `AMonocle` as a `Grate`. -}
monGrate :: AMonocle s t a b -> Grate s t a b
monGrate = cloneGrate . cloneMonocle

{- | The unit `Monocle`. -}
monocle0 :: Monocle () () a b
monocle0 _ = pureP (pure ())

{- | The pair `Monocle`. -}
monocle2 :: Monocle (a,a) (b,b) a b
monocle2 p = dimap2 fst snd (liftA2 (,)) p p

{- | A `Monocle` for each homogeneous tuple `V` @(n :: Peano)@. -}
class MonocleN (n :: Peano) where
  monocleV :: Monocle (V n a) (V n b) a b
instance MonocleN Z where
  monocleV _ = pureP (pure VNil)
instance MonocleN n => MonocleN (S n) where
  monocleV p = dimap2
    (\(a :>< _) -> a)
    (\(_ :>< v) -> v)
    (liftA2 (:><))
    p (monocleV @n p)

type Grate s t a b = forall p f.
  ( Closed p
  , Monoidal p
  , forall x. (Distributive (p x))
  , forall x. (Applicative (p x))
  , Distributive f
  , Applicative f
  ) => p a (f b) -> p s (f t)

type Grate' s a = Grate s s a a

type AGrate s t a b =
  Grating a b a (Identity b) -> Grating a b s (Identity t)

type AGrate' s a = AGrate s s a a

cotraversed :: Distributive g => Grate (g a) (g b) a b
cotraversed = grate $ flip cotraverse id

represented :: Representable g => Grate (g a) (g b) a b
represented = grate $ tabulate . (. flip index)

grate :: (((s -> a) -> b) -> t) -> Grate s t a b
grate f = dimap (&) (cotraverse f) . closed

withGrate :: AGrate s t a b -> ((s -> a) -> b) -> t
withGrate grt = unGrating $ runIdentity <$> grt (Identity <$> anyToken)

cloneGrate :: AGrate s t a b -> Grate s t a b
cloneGrate grt = grate (withGrate grt)

closing :: Closed p => AGrate s t a b -> p a b -> p s t
closing grt = dimap (&) (withGrate grt) . closed

distributing
  :: (Closed p, Distributive g)
  => AGrate s t a b -> p a (g b) -> g (p s t)
distributing grt
  = fmap unWrapMonoidal
  . distribute
  . dimap (&) (cotraverse (withGrate grt))
  . closed
  . WrapMonoidal

cotraverseOf :: Functor f => AGrate s t a b -> (f a -> b) -> f s -> t
cotraverseOf grt = runCostar . closing grt . Costar

distributeOf :: Functor f => AGrate s t b (f b) -> f s -> t
distributeOf grt = cotraverseOf grt id

collectOf :: Functor f => AGrate s t b (f b) -> (a -> s) -> f a -> t
collectOf grt f = distributeOf grt . fmap f
