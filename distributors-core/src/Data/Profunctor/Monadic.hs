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

For qualified do-notation, with pattern bonding,
import "Data.Profunctor.Monadic.Do" qualified;
this module has no names which conflict with the "Prelude".
-}

module Data.Profunctor.Monadic
  ( -- * Monadic
    Monadic
    -- * MonadicTrans
  , MonadicTrans (..)
  ) where

import Control.Monad (join)
import Data.Profunctor (Profunctor)

{- | A `Profunctor` which is also a `Monad`. -}
type Monadic p = (Profunctor p, forall x. Monad (p x))

{- | A `MonadicTrans` profunctor transforms a monad @m@,
like a `Control.Monad.Trans.Class.MonadTrans`, so that its actions
may run effects of @m@ forwards, by `liftP`,
& absorb them backwards, by `joinP`.

`liftP` is a monad morphism.
-}
class
  ( forall m x. Monad m => Monad (p m x)
  , forall m. Monad m => Profunctor (p m)
  ) => MonadicTrans p where
  liftP :: Monad m => m b -> p m a b
  liftP = joinP . return
  joinP :: Monad m => p m a (m b) -> p m a b
  joinP = join . fmap liftP
  {-# MINIMAL liftP | joinP #-}
