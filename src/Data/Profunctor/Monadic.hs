{-|
Module      : Data.Profunctor.Monadic
Description : distributors
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Data.Profunctor.Monadic
  ( Monadic
  , return
  , (>>=)
  , (>>)
  ) where

import Control.Monad hiding ((>>), (>>=))
import Data.Profunctor
import qualified Prelude as P ((>>), (>>=))
import Prelude hiding ((>>), (>>=))

type Monadic p = (Profunctor p, forall x. Monad (p x))

(>>) :: Monadic p => p () c -> p a b -> p a b
x >> y = lmap (const ()) x P.>> y

(>>=) :: Monadic p => p a a -> (a -> p a a) -> p a a
(>>=) = (P.>>=)
