{- |
Module      : Control.Lens.Diopter
Description : diopters
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Control.Lens.Diopter
  ( -- * Diopter
    Diopter
  , ADiopter
    -- * Combinators
  , diopter
  , withDiopter
  , cloneDiopter
  , mapDiopter
  , optioned
  , manied
  , homogenized
    -- * Dioptrice
  , Dioptrice (..), runDioptrice
  ) where

import Control.Lens
import Control.Lens.Internal.Profunctor
import Data.Profunctor.Distributor
import Data.Void
import GHC.Generics

{- | `Diopter`s are an optic that generalizes
`Control.Lens.Bifocal.Bifocal`s and `Control.Lens.Traversal.Traversal`s.

Every `Control.Lens.Iso.Iso` and `Control.Lens.Monocle` is a `Diopter`.

`Diopter`s are isomorphic to `Dioptrice`s.
-}
type Diopter s t a b = forall p f.
  (Distributor p, Applicative f)
    => p a (f b) -> p s (f t)

{- | If you see `ADiopter` in a signature for a function,
the function is expecting a `Diopter`. -}
type ADiopter s t a b =
  Dioptrice a b a (Identity b) -> Dioptrice a b s (Identity t)

{- | Build a `Diopter`. -}
diopter :: Homogeneous h => (s -> h a) -> (h b -> t) -> Diopter s t a b
diopter f g = unwrapPafb . runDioptrice (Dioptrice f g) . WrapPafb

{- | Convert `ADiopter` to the pair of functions that characterize it. -}
withDiopter
  :: ADiopter s t a b
  -> (forall h. Homogeneous h => (s -> h a) -> (h b -> t) -> r)
  -> r
withDiopter dio k = case (runIdentity <$> dio (Identity <$> anyToken)) of
  Dioptrice f g -> k f g

{- | Action of `ADiopter` on `Distributor`s. -}
mapDiopter :: Distributor p => ADiopter s t a b -> p a b -> p s t
mapDiopter dio = withDiopter dio $ \f g -> dimap f g . homogeneously

{- | Clone `ADiopter` so that you can reuse the same
monomorphically typed `Diopter` for different purposes.
-}
cloneDiopter :: ADiopter s t a b -> Diopter s t a b
cloneDiopter dio = withDiopter dio diopter

{- | One or none. -}
optioned :: Diopter (Maybe a) (Maybe b) a b
optioned = unwrapPafb . optionalP . WrapPafb

{- | Zero or more. -}
manied :: Diopter [a] [b] a b
manied = unwrapPafb . manyP . WrapPafb

{- | Build a `Diopter` from a `Homogeneous`
countable sum of countable products.

prop> traverse = homogenized
prop> homogenized = ditraversed
-}
homogenized :: Homogeneous t => Diopter (t a) (t b) a b
homogenized = unwrapPafb . homogeneously . WrapPafb

{- | A `Dioptrice` provides efficient access
to some pair of functions that make up a `Diopter`.
-}
data Dioptrice a b s t where
  Dioptrice
    :: Homogeneous h
    => (s -> h a)
    -> (h b -> t)
    -> Dioptrice a b s t
instance Tokenized a b (Dioptrice a b) where
  anyToken = Dioptrice Par1 unPar1
instance Profunctor (Dioptrice a b) where
  dimap f g (Dioptrice sa bt) = Dioptrice (sa . f) (g . bt)
instance Functor (Dioptrice a b s) where fmap = rmap
instance Applicative (Dioptrice a b s) where
  pure t = Dioptrice (const U1) (const t)
  Dioptrice fx gx <*> Dioptrice fy gy = Dioptrice
    (\s -> fx s :*: fy s)
    (\(h :*: g) -> gx h (gy g))
instance Distributor (Dioptrice a b) where
  zeroP = Dioptrice absurd ridiculous
    where
      ridiculous :: V1 b -> x
      ridiculous = (\case)
  Dioptrice fx gx >+< Dioptrice fy gy = Dioptrice
    (either (L1 . fx) (R1 . fy))
    (\case {L1 h -> Left (gx h); R1 j -> Right (gy j)})
  optionalP (Dioptrice f g) = Dioptrice
    (Comp1 . fmap f)
    (fmap g . unComp1)
  manyP (Dioptrice f g) = Dioptrice
    (Comp1 . fmap f)
    (fmap g . unComp1)

{- | Run a `Dioptrice` on a `Distributor`. -}
runDioptrice
  :: Distributor p
  => Dioptrice a b s t
  -> p a b -> p s t
runDioptrice (Dioptrice f g) = dimap f g . homogeneously
