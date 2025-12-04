module Control.Lens.Grammar.Symbol
  ( TerminalSymbol (..)
  , NonTerminalSymbol (..)
  ) where

import Control.Lens.Internal.Equator
import Data.Profunctor
import Data.Profunctor.Monoidal

class TerminalSymbol token s where
  terminal :: [token] -> s
  default terminal
    :: (p () () ~ s, Eq token, Equator token token p, Monoidal p, Cochoice p)
    => [token] -> s
  terminal = equator

instance TerminalSymbol a [a] where
  terminal = id

class NonTerminalSymbol s where
  nonTerminal :: String -> s
