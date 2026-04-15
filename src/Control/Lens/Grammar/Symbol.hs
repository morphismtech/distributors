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
import Data.Bifunctor.Joker
import Data.Profunctor
import Data.Profunctor.Monoidal

-- | A `terminal` symbol in a grammar.
class TerminalSymbol token s | s -> token where
  terminal :: [token] -> s
  default terminal
    :: (p () () ~ s, Tokenized token (p token token), Monoidal p, Choice p, Cochoice p)
    => [token] -> s
  terminal str = only str ?< tokens str

-- | A `nonTerminal` symbol in a grammar.
class NonTerminalSymbol s where
  nonTerminal :: String -> s

-- instances
instance TerminalSymbol token (f ())
  => TerminalSymbol token (Joker f () ()) where
    terminal = Joker . terminal @token
