{-|
Module      : Data.Profunctor.Distributor
Description : distributive profunctors
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Data.Profunctor.Distributor
  ( Monoidal, oneP, (>*<), dimap2, (>*), (*<)
  , Distributor (zeroP, (>+<), optionalP, manyP), dialt
  , Alternator (alternate, someP)
  , Filtrator (filtrate)
  , dimapMaybe
  ) where

import Control.Applicative
import Control.Arrow
import Control.Lens
import Data.Profunctor
import Data.Void
import Witherable

type Monoidal p = (Profunctor p, forall x. Applicative (p x))

oneP :: Monoidal p => p () ()
oneP = pure ()

(>*<) :: Monoidal p => p a b -> p c d -> p (a,c) (b,d)
(>*<) = dimap2 fst snd (,)

dimap2
  :: Monoidal p
  => (s -> a)
  -> (s -> c)
  -> (b -> d -> t)
  -> p a b -> p c d -> p s t
dimap2 f g h p q = liftA2 h (lmap f p) (lmap g q)

(>*) :: Monoidal p => p () c -> p a b -> p a b
x >* y = lmap (const ()) x *> y

(*<) :: Monoidal p => p a b -> p () c -> p a b
x *< y = x <* lmap (const ()) y

class Monoidal p => Distributor p where

  zeroP :: p Void Void
  default zeroP :: Alternator p => p Void Void
  zeroP = empty

  (>+<) :: p a b -> p c d -> p (Either a c) (Either b d)
  default (>+<)
    :: Alternator p
    => p a b -> p c d -> p (Either a c) (Either b d)
  x >+< y = alternate (Left x) <|> alternate (Right y)

  optionalP :: p a b -> p (Maybe a) (Maybe b)
  optionalP = dialt
    (maybe (Left ()) Right)
    (const Nothing)
    Just
    oneP

  manyP :: p a b -> p [a] [b]
  manyP p = dialt
    (maybe (Left ()) Right . uncons)
    (const [])
    (uncurry (:))
    oneP
    (p >*< manyP p)

dialt
  :: Distributor p
  => (s -> Either a c)
  -> (b -> t)
  -> (d -> t)
  -> p a b -> p c d -> p s t
dialt f g h p q = dimap f (either g h) (p >+< q)

class (Choice p, Distributor p, forall x. Alternative (p x))
  => Alternator p where

    alternate
      :: Either (p a b) (p c d)
      -> p (Either a c) (Either b d)
    default alternate
      :: Cochoice p
      => Either (p a b) (p c d)
      -> p (Either a c) (Either b d)
    alternate =
      dimapMaybe (either Just (pure Nothing)) (Just . Left)
      |||
      dimapMaybe (either (pure Nothing) Just) (Just . Right)

    someP :: p a b -> p [a] [b]
    someP p = mapPrism _Cons (p >*< manyP p) where
      mapPrism pat = withPrism pat $ \f g ->
        dimap g (either id f) . right'

class (Cochoice p, forall x. Filterable (p x))
  => Filtrator p where

    filtrate
      :: p (Either a c) (Either b d)
      -> (p a b, p c d)
    default filtrate
      :: Choice p
      => p (Either a c) (Either b d)
      -> (p a b, p c d)
    filtrate =
      dimapMaybe (Just . Left) (either Just (pure Nothing))
      &&&
      dimapMaybe (Just . Right) (either (pure Nothing) Just)

dimapMaybe
  :: (Choice p, Cochoice p)
  => (s -> Maybe a) -> (b -> Maybe t)
  -> p a b -> p s t
dimapMaybe f g =
  let
    m2e h = maybe (Left ()) Right . h
    fg = dimap (>>= m2e f) (>>= m2e g)
  in
    unright . fg . right'
