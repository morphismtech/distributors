{-|
Module      : Control.Lens.Grammar
Description : monadic pair-bonding do-notation
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Control.Lens.Grammar.Do
  ( -- *
    (>>=)
  , (>>)
  , (<$>)
  , fail
  , return
  ) where

import Control.Applicative (Alternative(empty))
import Control.Lens (Optic)
import Control.Lens.Grammar.BackusNaur (BackusNaurForm (rule))
import Control.Monad (join)
import Data.Profunctor (Profunctor (dimap))
import Data.Profunctor.Monadic (Monadic (liftP, bondM))
import Prelude (Applicative (pure), const, fmap, fst, snd, return, (.), String)

(>>=) :: Monadic m p => p m a a -> (a -> p m b c) -> p m (a,b) (a,c)
infixl 1 >>=
(>>=) = bondM

(>>) :: Monadic m p => p m () () -> p m b c -> p m b c
infixl 1 >>
x >> y = dimap ((),) snd (x >>= const y)

(<$>)
  :: (Monadic m p, Applicative m)
  => Optic (p m) m s t a b
  -> p m (a,()) (b,()) -> p m s t
infixl 4 <$>
f <$> x = join (fmap liftP (f (dimap (,()) (pure . fst) x)))

fail :: (Alternative f, BackusNaurForm (f a)) => String -> f a
fail msg = rule msg empty
