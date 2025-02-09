{- |
Module      : Control.Lens.Token
Description : tokens
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Control.Lens.Token
  ( Tokenized (anyToken)
  , token
  , tokens
  , satisfy
  , restOfTokens
  , endOfTokens
  ) where

import Control.Lens
import Control.Lens.Internal.Iso
import Control.Lens.Internal.Prism
import Control.Lens.PartialIso
import Data.Profunctor
import Data.Profunctor.Distributor

class Tokenized a b p | p -> a, p -> b where
  anyToken :: p a b
instance Tokenized a b (Identical a b) where
  anyToken = Identical
instance Tokenized a b (Exchange a b) where
  anyToken = Exchange id id
instance Tokenized a b (Market a b) where
  anyToken = Market id Right
instance Tokenized a b (PartialExchange a b) where
  anyToken = PartialExchange Just Just

token :: (Cochoice p, Eq c, Tokenized c c p) => c -> p () ()
token c = only c ?< anyToken

tokens :: (Cochoice p, Monoidal p, Eq c, Tokenized c c p) => [c] -> p () ()
tokens [] = oneP
tokens (c:cs) = token c *> tokens cs

satisfy :: (Choice p, Cochoice p, Tokenized c c p) => (c -> Bool) -> p c c
satisfy f = _Satisfy f >?< anyToken

restOfTokens :: (Distributor p, Tokenized c c p) => p [c] [c]
restOfTokens = manyP anyToken

endOfTokens :: (Cochoice p, Distributor p, Tokenized c c p) => p () ()
endOfTokens = _Empty ?< restOfTokens
