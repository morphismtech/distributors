{- |
Module      : Control.Lens.Grammar.Boole
Description : Boolean algebras
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable

See Boole, [The Mathematical Analysis of Logic]
(https://www.gutenberg.org/files/36884/36884-pdf.pdf).
-}

module Control.Lens.Grammar.Boole
  ( -- * BooleanAlgebra
    BooleanAlgebra (..)
  , andB, orB, allB, anyB
  ) where

import Data.Foldable
import Data.Monoid

-- | A `BooleanAlgebra`, like `Bool`, supporting classical logical operations.
class BooleanAlgebra b where

  -- | conjunction
  (>&&<) :: b -> b -> b
  default (>&&<)
    :: (b ~ f bool, BooleanAlgebra bool, Applicative f) => b -> b -> b
  (>&&<) = liftA2 (>&&<)

  -- | disjunction
  (>||<) :: b -> b -> b
  default (>||<)
    :: (b ~ f bool, BooleanAlgebra bool, Applicative f) => b -> b -> b
  (>||<) = liftA2 (>||<)

  -- | negation
  notB :: b -> b
  default notB
    :: (b ~ f bool, BooleanAlgebra bool, Functor f) => b -> b
  notB = fmap notB

  -- | true
  trueB :: b
  default trueB
    :: (b ~ f bool, BooleanAlgebra bool, Applicative f) => b
  trueB = pure trueB

  -- | false
  falseB :: b
  default falseB
    :: (b ~ f bool, BooleanAlgebra bool, Applicative f) => b
  falseB = pure falseB

-- | cumulative conjunction
andB :: (Foldable f, BooleanAlgebra b) => f b -> b
andB = foldl' (>&&<) trueB

-- | cumulative disjunction
orB :: (Foldable f, BooleanAlgebra b) => f b -> b
orB = foldl' (>||<) falseB

-- | universal
allB :: (Foldable f, BooleanAlgebra b) => (a -> b) -> f a -> b
allB f = foldl' (\b a -> b >&&< f a) trueB

-- | existential
anyB :: (Foldable f, BooleanAlgebra b) => (a -> b) -> f a -> b
anyB f = foldl' (\b a -> b >||< f a) falseB

--instances
instance BooleanAlgebra (x -> Bool)
instance (Applicative f, BooleanAlgebra bool)
  => BooleanAlgebra (Ap f bool)
instance BooleanAlgebra Bool where
  falseB = False
  trueB = True
  notB = not
  (>&&<) = (&&)
  (>||<) = (||)
