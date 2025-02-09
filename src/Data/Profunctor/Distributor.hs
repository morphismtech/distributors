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
  ( Monoidal, oneP, (>*<), dimap2, (>*), (*<), replicateP, foreverP
  , Distributor (zeroP, (>+<), optionalP, manyP), dialt
  , Alternator (alternate, someP)
  , Filtrator (filtrate)
  , Tokenized (anyToken), token, tokens, satisfy, restOfTokens, endOfTokens
  , SepBy (..), sepBy, atLeast0, atLeast1, dichainl1, dichainr1
  ) where

import Control.Applicative
import Control.Arrow
import Control.Lens hiding (chosen)
import Control.Lens.Internal.Iso
import Control.Lens.Internal.Prism
import Control.Lens.Internal.Profunctor
import Control.Lens.PartialIso
import Data.Bifunctor.Clown
import Data.Bifunctor.Joker
import Data.Distributive
import Data.Functor.Compose
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
infixl 5 >*

(*<) :: Monoidal p => p a b -> p () c -> p a b
x *< y = x <* lmap (const ()) y
infixl 5 *<

foreverP :: Monoidal p => p () c -> p a b
foreverP a = let a' = a >* a' in a'

-- thanks to Fy on Monoidal Café Discord
replicateP
  :: (Monoidal p, Traversable t, Distributive t)
  => p a b -> p (t a) (t b)
replicateP p = traverse (\f -> lmap f p) (distribute id)

class Monoidal p => Distributor p where

  zeroP :: p Void Void
  default zeroP :: Alternator p => p Void Void
  zeroP = empty

  (>+<) :: p a b -> p c d -> p (Either a c) (Either b d)
  default (>+<)
    :: Alternator p
    => p a b -> p c d -> p (Either a c) (Either b d)
  x >+< y = alternate (Left x) <|> alternate (Right y)
  infixr 3 >+<

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

class Tokenized a b p | p -> a, p -> b where
  anyToken :: p a b
instance Tokenized a b (Identical a b) where
  anyToken = Identical
instance Tokenized a b (Exchange a b) where
  anyToken = Exchange id id
instance Tokenized a b (Market a b) where
  anyToken = Market id Right
instance Tokenized a b (PartialExchange a b) where
  anyToken = PartialExchange Just Just

token :: (Cochoice p, Eq c, Tokenized c c p) => c -> p () ()
token c = only c ?< anyToken

tokens :: (Cochoice p, Monoidal p, Eq c, Tokenized c c p) => [c] -> p () ()
tokens [] = oneP
tokens (c:cs) = token c *> tokens cs

satisfy :: (Choice p, Cochoice p, Tokenized c c p) => (c -> Bool) -> p c c
satisfy f = _Satisfy f >?< anyToken

restOfTokens :: (Distributor p, Tokenized c c p) => p [c] [c]
restOfTokens = manyP anyToken

endOfTokens :: (Cochoice p, Distributor p, Tokenized c c p) => p () ()
endOfTokens = _Empty ?< restOfTokens

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

dichainl1
  :: (Alternator p, Filtrator p)
  => APartialIso a b (a,a) (b,b) -> SepBy p -> p a b -> p a b
dichainl1 pat sep p =
  coPartialIso (difoldl (coPartialIso pat)) >?<
    beginBy sep >* p >*< manyP (separateBy sep >* p) *< endBy sep

dichainr1
  :: (Alternator p, Filtrator p)
  => APartialIso a b (a,a) (b,b) -> SepBy p -> p a b -> p a b
dichainr1 pat sep p =
  coPartialIso (difoldr (coPartialIso pat)) >?<
    beginBy sep >* manyP (p *< separateBy sep) >*< p *< endBy sep

-- ORPHANAGE --

instance Monoid r => Applicative (Forget r a) where
  pure _ = Forget mempty
  Forget f <*> Forget g = Forget (f <> g)
instance Decidable f => Applicative (Clown f a) where
  pure _ = Clown conquer
  Clown x <*> Clown y = Clown (divide (id &&& id) x y)
deriving newtype instance Applicative f => Applicative (Joker f a)
instance (Profunctor p, Functor f)
  => Functor (WrappedPafb f p a) where fmap = rmap
deriving via Compose (p a) f instance
  (Monoidal p, Applicative f)
    => Applicative (WrappedPafb f p a)
deriving via Compose (p a) f instance
  (Profunctor p, forall x. Alternative (p x), Applicative f)
    => Alternative (WrappedPafb f p a)
deriving via Compose (p a) f instance
  (Profunctor p, forall x. Functor (p x), Filterable f)
    => Filterable (WrappedPafb f p a)
instance (Distributor p, Applicative f)
  => Distributor (WrappedPafb f p) where
    zeroP = WrapPafb (rmap pure zeroP)
    WrapPafb x >+< WrapPafb y = WrapPafb $
      dialt id (fmap Left) (fmap Right) x y
    -- manyP
    -- optionalP
instance (Profunctor p, Filterable f)
  => Cochoice (WrappedPafb f p) where
    unleft (WrapPafb p) = WrapPafb $
      dimap Left (mapMaybe (either Just (const Nothing))) p
    unright (WrapPafb p) = WrapPafb $
      dimap Right (mapMaybe (either (const Nothing) Just)) p
instance (Closed p, Distributive f)
  => Closed (WrappedPafb f p) where
    closed (WrapPafb p) = WrapPafb (rmap distribute (closed p))
instance (Alternator p, Alternative f)
  => Alternator (WrappedPafb f p) where
    alternate =
      let
        f = WrapPafb
          . rmap (either (fmap Left) pure)
          . alternate
          . Left
          . unwrapPafb
        g = WrapPafb
          . rmap (either pure (fmap Right))
          . alternate
          . Right
          . unwrapPafb
      in
        either f g
    -- someP
instance (Filtrator p, Filterable f)
  => Filtrator (WrappedPafb f p) where
    filtrate (WrapPafb p) =
      let
        fL = Left . mapMaybe (either Just (const Nothing))
        fR = Right . mapMaybe (either (const Nothing) Just)
        (pL,_) = filtrate (rmap fL p)
        (_,pR) = filtrate (rmap fR p)
      in
        ( WrapPafb pL
        , WrapPafb pR
        )
