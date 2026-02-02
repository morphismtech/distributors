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
  ( TerminalSymbol (..)
  , NonTerminalSymbol (..)
  ) where

import Control.Lens.Grammar.Token
import Data.Profunctor
import Data.Profunctor.Monoidal
import qualified Data.Sequence as Seq
import qualified Data.Vector as Vec
import qualified Data.Text as Strict
import qualified Data.Text.Lazy as Lazy

class TerminalSymbol token s where
  terminal :: [token] -> s
  default terminal
    :: (p () () ~ s, Tokenized token (p token token), Monoidal p, Cochoice p)
    => [token] -> s
  terminal = terminator

instance TerminalSymbol a [a] where
  terminal = id
instance TerminalSymbol a (Vec.Vector a) where
  terminal = Vec.fromList
instance TerminalSymbol a (Seq.Seq a) where
  terminal = Seq.fromList
instance TerminalSymbol Char Lazy.Text where
  terminal = Lazy.pack
instance TerminalSymbol Char Strict.Text where
  terminal = Strict.pack

class NonTerminalSymbol s where
  nonTerminal :: String -> s
