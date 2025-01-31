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
  , Stream
  , ShowRead (ShowRead)
  ) where

import Control.Applicative
import Control.Arrow
import Control.Lens
import Control.Lens.PartialIso
import Control.Lens.Token
import Data.Profunctor
import Data.Void
import Text.ParserCombinators.ReadP
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

  manyP :: Stream s t a b => p a b -> p s t
  manyP p = dialt
    (maybe (Left ()) Right . uncons)
    (const Empty)
    (review _Cons)
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

    someP :: Stream s t a b => p a b -> p s t
    someP p = _Cons >? p >*< manyP p

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

type Stream s t a b =
  ( Cons s t a b
  , AsEmpty s
  , Cons s s a a
  , AsEmpty t
  , Cons t t b b
  )

data ShowRead a b = ShowRead (a -> Maybe ShowS) (ReadP b)
instance Tokenized Char Char ShowRead where
  anyToken = ShowRead (Just . (:)) get
instance Profunctor ShowRead where
  dimap f g (ShowRead s r) = ShowRead (s . f) (g <$> r)
instance Functor (ShowRead a) where fmap = rmap
instance Applicative (ShowRead a) where
  pure b = ShowRead (const (Just id)) (pure b)
  ShowRead s0 r0 <*> ShowRead s1 r1 =
    ShowRead (liftA2 (liftA2 (.)) s1 s0) (r0 <*> r1)
instance Alternative (ShowRead a) where
  empty = ShowRead (const Nothing) empty
  ShowRead s0 r0 <|> ShowRead s1 r1 =
    ShowRead (liftA2 (<|>) s0 s1) (r0 <|> r1)
instance Choice ShowRead where
  left' (ShowRead s r) =
    ShowRead (either s (const Nothing)) (Left <$> r)
  right' (ShowRead s r) =
    ShowRead (either (const Nothing) s) (Right <$> r)
instance Cochoice ShowRead where
  unleft (ShowRead s r) =
    ShowRead (s . Left) (r >>= either pure (const empty))
  unright (ShowRead s r) =
    ShowRead (s . Right) (r >>= either (const empty) pure)
instance Distributor ShowRead
instance Alternator ShowRead
instance Filtrator ShowRead
instance Filterable (ShowRead a) where
  mapMaybe = dimapMaybe Just
