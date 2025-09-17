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
import Data.Profunctor.Monadic

type MLens s t a b = forall p f. (Monadic p, Monad f) => p a (f b) -> p s (f t)

data Monastery s t a b = Monastery (s -> (b,s)) (a -> (b, t -> t))
instance Functor (Monastery s t a) where fmap = rmap
instance Applicative (Monastery s t a) where
  pure b = Monastery (\s -> (b,s)) (\_ -> (b, id))
  Monastery getf putf <*> Monastery geta puta =
    Monastery
      (\s -> let (f, s') = getf s; (a, s'') = geta s' in (f a, s''))
      (\x -> let (f, r) = putf x; (a, r') = puta x in (f a, r' . r))
instance Monad (Monastery s t a) where
  return = pure
  Monastery get put >>= f = Monastery
    (\s -> let Monastery get' _ = f (fst (get s)) in get' s)
    (\x -> let (a,r) = put x; Monastery _ put' = f a; (b, r') = put' x in (b, r' . r))
instance Profunctor (Monastery s t) where
  dimap f g (Monastery get put) = Monastery
    (first' g . get)
    (first' g . put . f)
