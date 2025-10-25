module Control.Lens.Grammar.Kleene
  ( KleeneStarAlgebra (..)
  ) where

class Monoid a => KleeneStarAlgebra a where
  starK :: a -> a
  plusK :: a -> a
  optK :: a -> a
  (>|<) :: a -> a -> a
  empK :: a
