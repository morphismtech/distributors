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
