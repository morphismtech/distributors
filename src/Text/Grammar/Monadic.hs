{-|
Module      : Text.Grammar.Monadic
Description : grammars
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Text.Grammar.Monadic
  ( GrammarM
  , GrammarrM
  , mgenReadS
  , mgenLint
  ) where

import Control.Applicative
import Control.Lens.Cons
import Data.Profunctor.Distributor
import Data.Profunctor.Monadic
import Text.Grammar.Distributor
import Witherable

type GrammarM a = forall p. (Grammatical p, Monadic p) => p a a

type GrammarrM a b = forall p. (Grammatical p, Monadic p) => p a a -> p b b

mgenReadS :: Grammar a -> ReadS a
mgenReadS = runParsor

mgenLint :: (Alternative f, Filterable f, Cons s s Char Char) => Grammar a -> a -> f (a, s -> s)
mgenLint = runLintor
