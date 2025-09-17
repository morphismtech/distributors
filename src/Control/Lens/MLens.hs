{- |
Module      : Control.Lens.MLens
Description : monocles
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Control.Lens.MLens
  ( MLens
  , Monastery (..)
  ) where

import Data.Profunctor
import Data.Profunctor.Distributor
import Data.Profunctor.Monadic

type MLens s t a b = forall p f. (Monadic p, Monad f) => p a (f b) -> p s (f t)

data Monastery a b s t = Monastery (b -> (t,b)) (s -> (t, a -> a))
instance Functor (Monastery a b s) where fmap = rmap
instance Applicative (Monastery a b s) where
  pure t = Monastery (\a -> (t,a)) (\_ -> (t,id))
  Monastery getf putf <*> Monastery geta puta =
    Monastery
      (\b -> let (f,b') = getf b; (x,b'') = geta b' in (f x, b''))
      (\s -> let (f,r) = putf s; (x,r') = puta s in (f x, r' . r))
instance Monad (Monastery a b s) where
  return = pure
  Monastery get put >>= f = Monastery
    (\b -> let Monastery get' _ = f (fst (get b)) in get' b)
    (\s -> let (x,r) = put s; Monastery _ put' = f x; (x', r') = put' s in (x', r' . r))
instance Profunctor (Monastery a b) where
  dimap f g (Monastery get put) = Monastery
    (first' g . get)
    (first' g . put . f)
instance Tokenized c c (Monastery c c) where
  anyToken = Monastery (\c -> (c,c)) (\c -> (c,id))
