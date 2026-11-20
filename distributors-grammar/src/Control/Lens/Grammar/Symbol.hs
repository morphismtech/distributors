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
    -- * Separators
  , sepWith
  ) where

import Control.Lens
import Control.Lens.PartialIso
import Control.Lens.Grammar.Token
import Control.Lens.Prismoid (Prismoid, sepBy)
import Data.Bifunctor.Joker
import Data.Profunctor
import Data.Profunctor.Distributor (Alternator)
import Data.Profunctor.Monoidal
import Text.ParserCombinators.ReadP (ReadP, string)

-- | A `terminal` symbol in a grammar.
class TerminalSymbol token s | s -> token where
  terminal :: [token] -> s
  default terminal
    :: (p () () ~ s, Tokenized token (p token token), Monoidal p, Choice p, Cochoice p)
    => [token] -> s
  terminal str = only str ?< tokens str

{- | `sepBy` a `terminal` separator, so a grammar separates foci
of a `Prismoid` by symbols.

> prop> sepWith str = sepBy (terminal str)
-}
sepWith
  :: (Alternator p, TerminalSymbol c (p () ()))
  => [c] -> Prismoid s t a b -> p a b -> p s t
sepWith = sepBy . terminal

-- | A `nonTerminal` symbol in a grammar.
class NonTerminalSymbol s where
  nonTerminal :: String -> s

-- instances
instance TerminalSymbol token (f ())
  => TerminalSymbol token (Joker f () ()) where
    terminal = Joker . terminal @token
instance TerminalSymbol Char (ReadP ()) where
  terminal str = string str *> pure ()
