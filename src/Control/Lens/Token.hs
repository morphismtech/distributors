{- |
Module      : Control.Lens.PartialIso
Description : partial isomorphisms
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Control.Lens.Token
  ( Tokenized (anyToken)
  , Token (Token)
  ) where

import Control.Lens
import Control.Lens.Internal.Iso
import Control.Lens.Internal.Prism

class Tokenized a b p | p -> a, p -> b where
  anyToken :: p a b
instance Tokenized a b (Identical a b) where
  anyToken = Identical
instance Tokenized a b (Exchange a b) where
  anyToken = Exchange id id
instance Tokenized a b (Market a b) where
  anyToken = Market id Right

data Token a b s t where
  Token :: Token a b a b
instance Tokenized a b (Token a b) where
  anyToken = Token
