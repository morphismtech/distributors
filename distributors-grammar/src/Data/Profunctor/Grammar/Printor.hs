{-|
Module      : Data.Profunctor.Grammar.Printor
Description : printor
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Data.Profunctor.Grammar.Printor
  ( -- * Printor
    Printor (..)
  , printP
  ) where

import Control.Applicative
import Control.Arrow
import Control.Category
import Control.Lens
import Control.Lens.Grammar.BackusNaur
import Control.Lens.Grammar.Symbol
import Control.Lens.Grammar.Token
import Control.Monad
import Data.Monoid.Disjunctive
import Data.Profunctor
import Data.Profunctor.Distributor
import Data.Profunctor.Monoidal.Cocartesian
import Data.Profunctor.Filtrator
import Data.Profunctor.Monoidal
import Data.Profunctor.Monadic (MonadicTrans (..))
import Data.Void
import Prelude hiding (id, (.))
import GHC.Exts
import Witherable (Filterable (..))

-- | t'Printor' is a simple printer `Profunctor`.
newtype Printor s f a b = Printor {runPrintor :: a -> f (b, s -> s)}

-- | Run the printer on a value, returning a function
-- that `cons`es tokens at the beginning of an input string,
-- from right to left.
printP :: Functor f => Printor s f a b -> a -> f (s -> s)
printP (Printor f) = fmap snd . f

-- Printor instances
instance Functor f => Functor (Printor s f a) where
  fmap f = Printor . fmap (fmap (first' f)) . runPrintor
instance Functor f => Profunctor (Printor s f) where
  dimap f g (Printor p) = Printor $ \a -> (\(b, q) -> (g b, q)) <$> p (f a)
  lmap f (Printor p) = Printor (p . f)
  rmap g (Printor p) = Printor $ \a -> (\(b, q) -> (g b, q)) <$> p a
instance Applicative f => Applicative (Printor s f a) where
  pure b = Printor (\_ -> pure (b, id))
  Printor f <*> Printor x = Printor $ \c ->
    liftA2 (\(g, p) (a, q) -> (g a, p . q)) (f c) (x c)
instance Alternative f => Alternative (Printor s f a) where
  empty = Printor (\_ -> empty)
  Printor p <|> Printor q = Printor (\a -> p a <|> q a)
instance Filterable f => Filterable (Printor s f a) where
  mapMaybe f (Printor p) = Printor $
    mapMaybe (\(a,q) -> fmap (, q) (f a)) . p
instance Monad f => Monad (Printor s f a) where
  return = pure
  Printor mx >>= f = Printor $ \a -> do
    (a1,g) <- mx a
    (b,h) <- runPrintor (f a1) a
    return (b, g . h)
instance (Alternative f, Monad f) => MonadPlus (Printor s f a)
instance MonadicTrans (Printor s) where
  liftP mb = Printor (\_ -> (, id) <$> mb)
instance Functor f => CocartesianMonoidal (Printor s f) where
  zeroP = Printor absurd
  Printor p >+< Printor q = Printor $
    either (fmap (first' Left) . p) (fmap (first' Right) . q)
{- | `manyP` & `optionalP` print their elements in turn,
rather than through isomorphisms & sums.
-}
instance Applicative f => Distributor (Printor s f) where
  manyP (Printor p) = Printor $ \as ->
    (\printed -> (map fst printed, \str -> foldr (\(_, q) -> q) str printed))
    <$> traverse p as
  optionalP (Printor p) = Printor $ \case
    Nothing -> pure (Nothing, id)
    Just a -> (\(b, q) -> (Just b, q)) <$> p a
instance Alternative f => DisjunctiveMonoid (Printor s f a b)
instance Alternative f => CocartesianChoice (Printor s f) where
  alternate = \case
    Left (Printor p) -> Printor $
      either (fmap (first' Left) . p) (\_ -> empty)
    Right (Printor p) -> Printor $
      either (\_ -> empty) (fmap (first' Right) . p)
instance Alternative f => Alternator (Printor s f) where
  optionP def p = pureP def <|> p
instance Filterable f => Filtrator (Printor s f) where
  filtrate (Printor p) =
    let
      leftMaybe = \case
        (Left b, q) -> Just (b, q)
        _ -> Nothing
      rightMaybe = \case
        (Right b, q) -> Just (b, q)
        _ -> Nothing
    in
      ( Printor (mapMaybe leftMaybe . p . Left)
      , Printor (mapMaybe rightMaybe . p . Right)
      )
instance Alternative f => Choice (Printor s f) where
  left' = alternate . Left
  right' = alternate . Right
instance Filterable f => Cochoice (Printor s f) where
  unleft = fst . filtrate
  unright = snd . filtrate
instance Functor f => Strong (Printor s f) where
  first' (Printor p) =
    Printor (\(a,c) -> fmap (\(b,q) -> ((b,c),q)) (p a))
  second' (Printor p) =
    Printor (\(c,a) -> fmap (\(b,q) -> ((c,b),q)) (p a))
instance Monad f => Category (Printor s f) where
  id = Printor $ \a -> return (a, id)
  Printor q . Printor p = Printor $ \a -> do
    (b, p') <- p a
    (c, q') <- q b
    return (c, q' . p')
instance Monad f => Arrow (Printor s f) where
  arr f = Printor (return . (, id) . f)
  (***) = (>*<)
  first = first'
  second = second'
instance (Alternative f, Monad f) => ArrowZero (Printor s f) where
  zeroArrow = empty
instance (Alternative f, Monad f) => ArrowPlus (Printor s f) where
  (<+>) = (<|>)
instance (Alternative f, Monad f) => ArrowChoice (Printor s f) where
  (+++) = (>+<)
  left = left'
  right = right'
instance
  ( Categorized a, a ~ Item s, IsList s, Cons s s a a
  , Filterable m, Alternative m, Monad m
  ) => Tokenized a (Printor s m a a) where
  {-# SPECIALISE instance Tokenized Char (Printor String Maybe Char Char) #-}
  anyToken = Printor (\b -> pure (b, cons b))
  token t = tokenClass (token t)
  oneOf ts = tokenClass (oneOf ts)
  notOneOf ts = tokenClass (notOneOf ts)
  asIn cat = tokenClass (asIn cat)
  notAsIn cat = tokenClass (notAsIn cat)
instance
  ( Categorized a, a ~ Item s, IsList s, Cons s s a a
  , Filterable m, Alternative m, Monad m
  ) => TokenAlgebra a (Printor s m a a) where
    {-# SPECIALISE instance
      TokenAlgebra Char (Printor String Maybe Char Char) #-}
    -- | The test is made once, rather than for each token.
    tokenClass test = matches `seq` Printor (\b ->
      if matches b then pure (b, cons b) else empty)
      where
        matches :: a -> Bool
        matches = tokenClass test
instance (a ~ Item s, Cons s s a a, Applicative m)
  => TerminalSymbol a (Printor s m () ()) where
    {-# SPECIALISE instance TerminalSymbol Char (Printor String Maybe () ()) #-}
    -- | Its tokens are printed together, rather than one at a time.
    terminal str = Printor (\_ -> pure ((), printed))
      where
        printed rest = foldr cons rest str
instance (Char ~ Item s, Cons s s Char Char, Applicative m)
  => IsString (Printor s m () ()) where
  fromString = terminal
instance
  ( Char ~ Item s, IsList s, Cons s s Char Char, AsEmpty s
  , Filterable m, Alternative m, Monad m
  ) => IsString (Printor s m s s) where
  fromString = tokens
instance Ruled (Printor s m a b)
instance BackusNaurForm (Printor s m a b)
instance Tried (Printor s m a b)
instance (Alternative m, Monad m) => MonadFail (Printor s m a) where
  fail _ = empty
