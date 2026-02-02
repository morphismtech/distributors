{-|
Module      : Data.Profunctor.Monadic
Description : monadic profunctors
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable

See Li-yao Xia, [Monadic profunctors for bidirectional programming]
(https://blog.poisson.chat/posts/2017-01-01-monadic-profunctors.html)

This module can provide qualified do-notation for `Monadic` profunctors.

>>> :set -XQualifiedDo
>>> import qualified Data.Profunctor.Monadic as P
-}

module Data.Profunctor.Monadic
  ( -- * Monadic
    Monadic
  , (>>=)
  , (>>)
  , fail
  , return
  ) where

import Data.Profunctor
import Prelude hiding ((>>=), (>>))

{- | A `Profunctor` which is also a `Monad`. -}
type Monadic p = (Profunctor p, forall x. Monad (p x))

{- | The pair bonding operator `>>=` is a context-sensitive
version of `Data.Profunctor.Monoidal.>*<`. -}
(>>=) :: Monadic p => p a b -> (b -> p c d) -> p (a,c) (b,d)
infixl 1 >>=
p >>= f = do
  b <- lmap fst p
  d <- lmap snd (f b)
  return (b,d)

{- | The unit bonding operator `>>`. -}
(>>) :: Monadic p => p () c -> p a b -> p a b
infixl 1 >>
x >> y = do _ <- lmap (const ()) x; y
