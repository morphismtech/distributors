{-|
Module      : Control.Monad.Fail.Try
Description : monads with fail and try semantics
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Control.Monad.Fail.Try
  ( MonadTry (..)
  , MonadFail (..)
  , MonadPlus (..)
  ) where

import Control.Monad

{- | `MonadTry` implements `fail` & `try` and
two alternation combinators
`Control.Applicative.<|>` & `mplus`.

The following invariants should hold.

prop> empty = mzero
prop> x <|> y = try x `mplus` y

prop> fail msg <|> x = x = x <|> fail msg

When a `MonadTry` is also a
`Control.Lens.Grammar.BackusNaur.BackusNaurForm`,
then the following invariant should hold.

prop> fail msg = rule msg empty

-}
class (MonadFail m, MonadPlus m) => MonadTry m where
  try :: m a -> m a
  default try :: m a -> m a
  try = id
