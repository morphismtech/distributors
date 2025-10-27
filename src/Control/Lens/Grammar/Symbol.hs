module Control.Lens.Grammar.Symbol
  ( Terminator
  , TerminalSymbol (..)
  , NonTerminalSymbol (..)
  ) where

import Control.Lens.Internal.Equator
import Data.Kind

type Terminator a p =
  ( a ~ Alphabet (p () ())
  , forall x y. (x ~ (), y ~ ()) => TerminalSymbol (p x y) :: Constraint
  )

class TerminalSymbol s where
  type Alphabet s
  terminal :: [Alphabet s] -> s
  default terminal
    :: (p () () ~ s, Equator' (Alphabet s) p)
    => [Alphabet s] -> s
  terminal = equator

instance TerminalSymbol [a] where
  type Alphabet [a] = a
  terminal = id

class NonTerminalSymbol a where
  nonTerminal :: String -> a
