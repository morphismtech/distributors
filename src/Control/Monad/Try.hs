module Control.Monad.Try
  ( MonadTry (..)
  , fail
  , mzero
  , mplus
  , mchoice
  ) where

import Control.Monad
import Data.Foldable

{- |

prop> x <|> y = try x `mplus` y
prop> fail msg <|> x = x = x <|> fail msg

-}
class (MonadFail m, MonadPlus m) => MonadTry m where
  try :: m a -> m a
  default try :: m a -> m a
  try = id

mchoice :: (Foldable f, MonadPlus p) => f (p a) -> p a
mchoice = foldl' mplus mzero
