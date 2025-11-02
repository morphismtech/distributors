module Control.Lens.Grammar.Context
  ( eof
  , ask
  ) where

import Control.Applicative
import Control.Lens
import Control.Monad
import Control.Monad.Reader

eof :: (AsEmpty s, MonadReader s m, Alternative m) => m ()
eof = do
  s <- ask
  when (isn't _Empty s) empty
