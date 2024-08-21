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
  , (>..<)
  , cloneMonocle
  , monTraversal
  , monClosed
  , monGrate
  , monBazaar
  , monCotraversal
  , monBitraversal
  ) where

import Control.Lens hiding (index, Traversing)
import Control.Lens.Internal.Context
import Control.Lens.Internal.FunList
import Data.Bifunctor.Biff
import Data.Profunctor
import Data.Profunctor.Monoidal

{- | A `Monocle` is a representation of a
fixed length homogeneous tuple isomorphism.

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
  Shop a b a (Identity b) -> Shop a b s (Identity t)

{- | A `Simple` `Monocle`. -}
type AMonocle' s a = AMonocle s s a a

{- | Turn a `AMonocle` into a curried homogeneous tuple isomorphism. -}
withMonocle :: AMonocle s t a b -> (Shop a b s t -> r) -> r
withMonocle mon k =
  k (runIdentity <$> mon (Identity <$> shop))

{- | Turn  a curried homogeneous tuple isomorphism, into a `Monocle`.-}
monocle :: Shop a b s t -> Monocle s t a b
monocle sh =
  cloneMonocle $ \p ->
    unWrapMonoidal $
      runShop (Identity <$> sh) $ \_ ->
        WrapMonoidal $ runIdentity <$> p

{- | The natural action of `AMonocle` on `Monoidal`. -}
(>..<) :: Monoidal p => AMonocle s t a b -> p a b -> p s t
mon >..< p =
  withMonocle mon $ \sh ->
    unWrapMonoidal . runShop sh $ \_ ->
      WrapMonoidal p

{- | `AMonocle` as a `Bitraversal`. -}
monBitraversal
  :: (Functor f, Applicative g, Monoidal p)
  => AMonocle s t a b
  -> p (f a) (g b) -> p (f s) (g t)
monBitraversal mon = runBiff . (mon >..<) . Biff

{- | Clone `AMonocle` as a `Monocle`. -}
cloneMonocle :: AMonocle s t a b -> Monocle s t a b
cloneMonocle mon
  = lmap Identity
  . monBitraversal mon
  . lmap runIdentity

{- | `AMonocle` as a lens-like `Control.Lens.Traversal.Traversal`. -}
monTraversal :: AMonocle s t a b -> Traversal s t a b
monTraversal = cloneMonocle

{- | `AMonocle` as a grate-like cotraversal. -}
monCotraversal
  :: (Functor f, Monoidal p)
  => AMonocle s t a b -> p (f a) b -> p (f s) t
monCotraversal mon
  = rmap runIdentity
  . monBitraversal mon
  . rmap Identity

{- | `AMonocle` can act as a grate on `Closed` profunctors. -}
monClosed :: Closed p => AMonocle s t a b -> p a b -> p s t
monClosed mon = dimap (&) (monCotraversal mon buy . Purchase) . closed

{- | `AMonocle` @s t a b@ as a function called a grate.

prop> ((s -> a) -> b) -> t ~ forall p. Closed p => p a b -> p s t
prop> ((s -> a) -> b) -> t ~ forall f. Functor f => (f a -> b) -> (f s -> t)
-}
monGrate :: AMonocle s t a b -> ((s -> a) -> b) -> t
monGrate mon = runCostar (mon >..< Costar buy) . Purchase

{- | `AMonocle` @s t a b@ as a function
@s -> ((a,..,a), b -> .. -> b -> t)@
-}
monBazaar :: AMonocle s t a b -> s -> Bazaar (->) a b t
monBazaar mon = runStar (mon >..< Star sell)

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
