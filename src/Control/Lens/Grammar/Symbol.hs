{- |
Module      : Control.Lens.Grammar.Symbol
Description : terminal & nonterminal symbols
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Control.Lens.Grammar.Symbol
  ( -- * Symbol
    TerminalSymbol (..)
  , NonTerminalSymbol (..)
  ) where

import Control.Lens
import Control.Lens.PartialIso
import Control.Lens.Grammar.Token
import Data.Profunctor
import Data.Profunctor.Monoidal

class TerminalSymbol token s | s -> token where
  terminal :: [token] -> s
  default terminal
    :: (p () () ~ s, Tokenized token (p token token), Monoidal p, Cochoice p)
    => [token] -> s
  terminal = foldr (\a p -> only a ?< anyToken *> p) oneP

class NonTerminalSymbol s where
  nonTerminal :: String -> s
