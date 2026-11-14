{-|
Module      : Data.Profunctor.Monadic.Do
Description : qualified do-notation for monadic profunctors
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable

Qualified do-notation for `Monadic` profunctors,
with pattern bonding, to import qualified.

>>> :set -XQualifiedDo
>>> import qualified Data.Profunctor.Monadic.Do as P

See "Control.Lens.Grammar#t:CtxGrammar" for
an example of how to use qualified do-notation
with pattern bonding.
-}

module Data.Profunctor.Monadic.Do
  ( (>>=)
  , (>>)
  , return
    -- | The "Prelude"'s, for patterns which may fail.
  , fail
  ) where

import Control.Lens
import Data.Profunctor.Monadic (Monadic)
import Data.Profunctor.Monoidal
import Prelude hiding ((>>=), (>>), return)

{- | The pair bonding operator @P.@`>>=` is a context-sensitive
version of `>*<`.

> prop> x >*< y = x P.>>= (\_ -> y)
-}
(>>=) :: Monadic p => p a b -> (b -> p c d) -> p (a,c) (b,d)
infixl 1 >>=
p >>= f = do
  b <- lmap fst p
  d <- lmap snd (f b)
  pure (b,d)

{- | @P.@`>>` sequences actions. -}
(>>) :: Monadic p => p () c -> p a b -> p a b
infixl 1 >>
x >> y = do _ <- lmap (const ()) x; y

{- | @P.@`return` is a `Monadic`-restricted
version of `pureP`.

> prop> pureP = P.return
-}
return :: (Monadic p, Choice p) => APrism a b () () -> p a b
return = pureP
