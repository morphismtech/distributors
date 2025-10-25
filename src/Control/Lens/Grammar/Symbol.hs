module Control.Lens.Grammar.Symbol
  ( Terminator
  , TerminalSymbol (..)
  , NonTerminalSymbol (..)
  ) where

import Control.Lens.Grammar.Equator
import Data.Kind
import Data.Profunctor
import Data.Profunctor.Monoidal

type Terminator a p =
  ( a ~ Alphabet (p () ())
  , forall x y. (x ~ (), y ~ ()) => TerminalSymbol (p x y)
  ) :: Constraint

class TerminalSymbol s where
  type Alphabet s
  terminal :: [Alphabet s] -> s
  default terminal
    :: ( Monoidal p, Cochoice p, p () () ~ s
       , Equator (Alphabet s) (Alphabet s) p
       , Eq (Alphabet s)
       )
    => [Alphabet s] -> s
  terminal = is

instance TerminalSymbol [a] where
  type Alphabet [a] = a
  terminal = id

class NonTerminalSymbol a where
  nonTerminal :: String -> a
