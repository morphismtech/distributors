{-|
Module      : Data.Profunctor.Monadic
Description : monadic profunctors
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Data.Profunctor.Monadic
  ( -- *
    Monadic
  , (>>=)
  , (>>)
  , fail
  , return
  ) where

import Data.Profunctor
import Prelude hiding ((>>=), (>>))

type Monadic p = (Profunctor p, forall x. Monad (p x))

{- | See Li-yao Xia [Monadic profunctors for bidirectional programming]
(https://blog.poisson.chat/posts/2017-01-01-monadic-profunctors.html)
-}
(>>=) :: Monadic p => p a b -> (b -> p c d) -> p (a,c) (b,d)
infixl 1 >>=
p >>= f = do
  b <- lmap fst p
  d <- lmap snd (f b)
  return (b,d)

(>>) :: Monadic p => p a b -> p () c -> p a b
infixl 1 >>
x >> y = dimap (,()) fst (x >>= const y)
