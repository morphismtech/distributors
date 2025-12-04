module Control.Lens.Grammar.Symbol
  ( TerminalSymbol (..)
  , NonTerminalSymbol (..)
  ) where

import Control.Lens.Grammar.Token
import Data.Profunctor
import Data.Profunctor.Monoidal

class TerminalSymbol token s where
  terminal :: [token] -> s
  default terminal
    :: (p () () ~ s, Tokenized token (p token token), Monoidal p, Cochoice p)
    => [token] -> s
  terminal = terminator

instance TerminalSymbol a [a] where
  terminal = id

class NonTerminalSymbol s where
  nonTerminal :: String -> s
