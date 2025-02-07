{-|
Module      : Data.Profunctor.Distributor
Description : lax monoidal & distributive profunctors
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Data.Profunctor.Distributor
  ( Monoidal, oneP, (>*<), dimap2, (>*), (*<)
  , Distributor (zeroP, (>+<), optionalP, manyP), dialt
  , Alternator (alternate, someP)
  , Filtrator (filtrate)
  , dimapMaybe
  , replicateP, foreverP
  , atLeast0, atLeast1, SepBy (..), sepBy
  ) where

import Control.Applicative
import Control.Arrow
import Data.Bifunctor.Clown
import Data.Bifunctor.Joker
import Data.Distributive
import Data.Functor.Contravariant.Divisible
import Data.Profunctor
import Data.Void
import Witherable

type Monoidal p = (Profunctor p, forall x. Applicative (p x))

oneP :: Monoidal p => p () ()
oneP = pure ()

(>*<) :: Monoidal p => p a b -> p c d -> p (a,c) (b,d)
(>*<) = dimap2 fst snd (,)
infixr 6 >*<

dimap2
  :: Monoidal p
  => (s -> a)
  -> (s -> c)
  -> (b -> d -> t)
  -> p a b -> p c d -> p s t
dimap2 f g h p q = liftA2 h (lmap f p) (lmap g q)

(>*) :: Monoidal p => p () c -> p a b -> p a b
x >* y = lmap (const ()) x *> y
infixr 6 >*

(*<) :: Monoidal p => p a b -> p () c -> p a b
x *< y = x <* lmap (const ()) y
infixr 6 *<

class Monoidal p => Distributor p where

  zeroP :: p Void Void
  default zeroP :: Alternator p => p Void Void
  zeroP = empty

  (>+<) :: p a b -> p c d -> p (Either a c) (Either b d)
  default (>+<)
    :: Alternator p
    => p a b -> p c d -> p (Either a c) (Either b d)
  x >+< y = alternate (Left x) <|> alternate (Right y)
  infixl 4 >+<

  optionalP :: p a b -> p (Maybe a) (Maybe b)
  optionalP = dialt (maybe (Left ()) Right) (const Nothing) Just oneP

  manyP :: p a b -> p [a] [b]
  manyP p = dialt unlist list0 list1 oneP (p >*< manyP p)

instance Distributor (->) where
  zeroP = id
  (>+<) = (+++)
instance Monoid s => Distributor (Forget s) where
  zeroP = Forget absurd
  Forget kL >+< Forget kR = Forget (either kL kR)
instance Decidable f => Distributor (Clown f) where
  zeroP = Clown lost
  Clown x >+< Clown y = Clown (chosen x y)
instance Alternative f => Distributor (Joker f) where
  zeroP = Joker empty
  Joker x >+< Joker y = Joker (Left <$> x <|> Right <$> y)

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
    someP p = dimap unlist (either list0 list1) (right' (p >*< manyP p))

unlist :: [a] -> Either () (a, [a])
unlist [] = Left ()
unlist (a:as) = Right (a,as)

list0 :: () -> [a]
list0 _ = []

list1 :: (a,[a]) -> [a]
list1 = uncurry (:)

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

foreverP :: Monoidal p => p () c -> p a b
foreverP a = let a' = a >* a' in a'

replicateP
  :: (Monoidal p, Traversable t, Distributive t)
  => p a b -> p (t a) (t b)
replicateP p = traverse (\f -> lmap f p) (distribute id)

atLeast0
  :: Distributor p
  => SepBy p -> p a b -> p [a] [b]
atLeast0 sep p =
  beginBy sep >* 
  dialt unlist list0 list1 oneP (p >*< manyP (separateBy sep >* p))
  *< endBy sep

atLeast1
  :: Alternator p
  => SepBy p -> p a b -> p [a] [b]
atLeast1 sep p = dimap unlist (either list0 list1)
  (right' (beginBy sep >* p >*< manyP (separateBy sep >* p) *< endBy sep))

{- | Used to parse multiple times, delimited by a `separateBy`,
a `beginBy`, and an `endBy`. -}
data SepBy p = SepBy
  { beginBy :: p () ()
  , endBy :: p () ()
  , separateBy :: p () ()
  }

{- | A default `SepBy` which can be modified by updating
`beginBy`, or `endBy` fields -}
sepBy :: Monoidal p => p () () -> SepBy p
sepBy = SepBy oneP oneP

-- ORPHANAGE --

instance Monoid r => Applicative (Forget r a) where
  pure _ = Forget mempty
  Forget f <*> Forget g = Forget (f <> g)

instance Decidable f => Applicative (Clown f a) where
  pure _ = Clown conquer
  Clown x <*> Clown y = Clown (divide (id &&& id) x y)

deriving newtype instance Applicative f => Applicative (Joker f a)
