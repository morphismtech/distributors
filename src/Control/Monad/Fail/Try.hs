{-|
Module      : Control.Monad.Fail.Try
Description : try & fail
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Control.Monad.Fail.Try
  ( -- * MonadTry
    MonadTry (..)
    -- * MonadFail
  , MonadFail (..)
    -- * MonadPlus
  , MonadPlus (..)
    -- * Alternative
  , Alternative (..)
    -- * Filterable
  , Filterable (..)
  ) where

import Control.Applicative
import Control.Lens.PartialIso ()
import Control.Monad
import Data.Bifunctor.Joker
import Witherable

{- | `MonadTry` is a failure handling interface, with `fail` & `try`
and redundant alternation & filtration operators.

prop> empty = mzero
prop> (<|>) = mplus
prop> filter = mfilter

When a `MonadTry` is also a
`Control.Lens.Grammar.BackusNaur.BackusNaurForm`,
then the following invariant should hold.

prop> fail label = rule label empty

-}
class (MonadFail m, MonadPlus m, Filterable m) => MonadTry m where

  {- | A handler for failures.
  Used for backtracking state on failure in
  `Data.Profunctor.Grammar.Parsector.Parsector`.
  -}
  try :: m a -> m a
  default try :: m a -> m a
  try = id

instance MonadTry m => MonadTry (Joker m a) where
  try = Joker . try . runJoker
