{-|
Module      : Data.Profunctor.Grammar
Description : grammar distributors
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Data.Profunctor.Grammar
  ( -- * Parsor
    Parsor (..)
  , unparseP
  , parseP
    -- * Printor
  , Printor (..)
  , printP
    -- * Grammor
  , Grammor (..)
  ) where

import Control.Applicative
import Control.Arrow
import Control.Category
import Control.Lens
import Control.Lens.Grammar.BackusNaur
import Control.Lens.Grammar.Boole
import Control.Lens.Grammar.Kleene
import Control.Lens.Grammar.Symbol
import Control.Lens.Grammar.Token
import Control.Monad
import Data.Coerce
import Data.Monoid
import Data.Profunctor
import Data.Profunctor.Distributor
import Data.Profunctor.Filtrator
import Data.Profunctor.Monoidal
import Data.Void
import Prelude hiding (id, (.))
import GHC.Exts
import Witherable

newtype Parsor s f a b = Parsor {runParsor :: Maybe a -> s -> f (b,s)}
parseP :: Parsor s f a b -> s -> f (b,s)
parseP (Parsor f) = f Nothing
unparseP :: Functor f => Parsor s f a b -> a -> s -> f s
unparseP (Parsor f) a = fmap snd . f (Just a)

newtype Printor s f a b = Printor {runPrintor :: a -> f (b, s -> s)}
printP :: Functor f => Printor s f a b -> a -> f (s -> s)
printP (Printor f) = fmap snd . f

newtype Grammor g a b = Grammor {runGrammor :: g}

-- Parsor instances
deriving stock instance Functor f => Functor (Parsor s f a)
instance Functor f => Profunctor (Parsor s f) where
  dimap f g = Parsor . dimap (fmap f) (fmap (fmap (first' g))) . runParsor
instance Monad m => Applicative (Parsor s m a) where
  pure b = Parsor (\_ s -> pure (b,s))
  Parsor f <*> Parsor x = Parsor $ \ma s -> do
    (g, s') <- f ma s
    (a, s'') <- x ma s'
    return (g a, s'')
instance (Alternative m, Monad m) => Strong (Parsor s m) where
  first' p = p >*< id
  second' p = id >*< p
instance Monad m => Monad (Parsor s m a) where
  return = pure
  Parsor p >>= f = Parsor $ \ma s -> do
    (a, s') <- p ma s
    runParsor (f a) ma s'
instance (Alternative m, Monad m) => Alternative (Parsor s m a) where
  empty = Parsor (\_ _ -> empty)
  Parsor p <|> Parsor q = Parsor $ \ma s -> p ma s <|> q ma s
instance (Alternative m, Monad m) => MonadPlus (Parsor s m a)
instance Filterable f => Filterable (Parsor s f a) where
  mapMaybe f (Parsor p) = Parsor $ \fa s ->
    mapMaybe (\(a,t) -> fmap (,t) (f a)) (p fa s)
instance Filterable f => Cochoice (Parsor s f) where
  unleft = fst . filtrate
  unright = snd . filtrate
instance Filterable f => Filtrator (Parsor s f) where
  filtrate (Parsor p) =
    ( Parsor $ \ma s -> mapMaybe
        (\case{(Left b,t) -> Just (b,t); _ -> Nothing})
        (p (fmap Left ma) s)
    , Parsor $ \ma s -> mapMaybe
        (\case{(Right b,t) -> Just (b,t); _ -> Nothing})
        (p (fmap Right ma) s)
    )
instance (Alternative m, Monad m) => Distributor (Parsor s m)
instance (Alternative m, Monad m) => Choice (Parsor s m) where
  left' = alternate . Left
  right' = alternate . Right
instance (Alternative m, Monad m) => Alternator (Parsor s m) where
  alternate = \case
    Left (Parsor p) -> Parsor $ \ma s -> case ma of
      Nothing -> fmap (first' Left) (p Nothing s)
      Just (Left a) -> fmap (first' Left) (p (Just a) s)
      Just (Right _) -> empty
    Right (Parsor p) -> Parsor $ \ma s -> case ma of
      Nothing -> fmap (first' Right) (p Nothing s)
      Just (Right a) -> fmap (first' Right) (p (Just a) s)
      Just (Left _) -> empty
instance (Alternative m, Monad m) => Category (Parsor s m) where
  id = Parsor $ \ma s -> case ma of
    Nothing -> empty
    Just a  -> pure (a,s)
  Parsor q . Parsor p = Parsor $ \ma s -> case ma of
    Nothing -> empty
    Just a -> do
      (b, t) <- p (Just a) s
      q (Just b) t
instance (Alternative m, Monad m) => Arrow (Parsor s m) where
  arr f = Parsor $ \ma s -> case ma of
    Nothing -> empty
    Just a  -> pure (f a, s)
  (***) = (>*<)
  first = first'
  second = second'
instance (Alternative m, Monad m) => ArrowZero (Parsor s m) where
  zeroArrow = empty
instance (Alternative m, Monad m) => ArrowPlus (Parsor s m) where
  (<+>) = (<|>)
instance (Alternative m, Monad m) => ArrowChoice (Parsor s m) where
  (+++) = (>+<)
  left = left'
  right = right'
instance
  ( Categorized a, a ~ Item s, IsList s
  , Cons s s a a, Snoc s s a a
  , Filterable m, Alternative m, Monad m
  ) => Tokenized a (Parsor s m a a) where
    anyToken = Parsor $ maybe
      (maybe empty pure . uncons)
      (\a -> pure . (a,) . flip snoc a)
instance
  ( Categorized a, a ~ Item s, IsList s
  , Cons s s a a, Snoc s s a a
  , Filterable m, Alternative m, Monad m
  ) => TokenAlgebra a (Parsor s m a a)
instance
  ( Categorized a, a ~ Item s, IsList s
  , Cons s s a a, Snoc s s a a
  , Filterable m, Alternative m, Monad m
  ) => TerminalSymbol a (Parsor s m () ()) where
instance
  ( Char ~ Item s, IsList s
  , Cons s s Char Char, Snoc s s Char Char
  , Filterable m, Alternative m, Monad m
  ) => IsString (Parsor s m () ()) where
  fromString = terminal
instance
  ( Char ~ Item s, IsList s
  , Cons s s Char Char, Snoc s s Char Char, AsEmpty s
  , Filterable m, Alternative m, Monad m
  ) => IsString (Parsor s m s s) where
  fromString = fromTokens
instance BackusNaurForm (Parsor s m a b)
instance (Alternative m, Monad m) => MonadFail (Parsor s m a) where
  fail _ = empty

-- Printor instances
instance Functor f => Functor (Printor s f a) where
  fmap f = Printor . fmap (fmap (first' f)) . runPrintor
instance Functor f => Profunctor (Printor s f) where
  dimap f g = Printor . dimap f (fmap (first' g)) . runPrintor
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
    return (b, h . g)
instance (Alternative f, Monad f) => MonadPlus (Printor s f a)
instance Applicative f => Distributor (Printor s f) where
  zeroP = Printor absurd
  Printor p >+< Printor q = Printor $
    either (fmap (first' Left) . p) (fmap (first' Right) . q)
instance Alternative f => Alternator (Printor s f) where
  alternate = \case
    Left (Printor p) -> Printor $
      either (fmap (first' Left) . p) (\_ -> empty)
    Right (Printor p) -> Printor $
      either (\_ -> empty) (fmap (first' Right) . p)
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
  anyToken = Printor (\b -> pure (b, cons b))
instance
  ( Categorized a, a ~ Item s, IsList s, Cons s s a a
  , Filterable m, Alternative m, Monad m
  ) => TokenAlgebra a (Printor s m a a)
instance
  ( Categorized a, a ~ Item s, IsList s, Cons s s a a
  , Filterable m, Alternative m, Monad m
  ) => TerminalSymbol a (Printor s m () ()) where
instance
  ( Char ~ Item s, IsList s, Cons s s Char Char
  , Filterable m, Alternative m, Monad m
  ) => IsString (Printor s m () ()) where
  fromString = terminal
instance
  ( Char ~ Item s, IsList s, Cons s s Char Char, AsEmpty s
  , Filterable m, Alternative m, Monad m
  ) => IsString (Printor s m s s) where
  fromString = fromTokens
instance BackusNaurForm (Printor s m a b)
instance (Alternative m, Monad m) => MonadFail (Printor s m a) where
  fail _ = empty

-- Grammor instances
instance Functor (Grammor g a) where fmap _ = coerce
instance Contravariant (Grammor g a) where contramap _ = coerce
instance Profunctor (Grammor g) where dimap _ _ = coerce
instance Bifunctor (Grammor g) where bimap _ _ = coerce
instance Choice (Grammor g) where
  left' = coerce
  right' = coerce
instance Monoid g => Applicative (Grammor g a) where
  pure _ = Grammor mempty
  Grammor rex1 <*> Grammor rex2 = Grammor (rex1 <> rex2)
instance KleeneStarAlgebra g => Alternative (Grammor g a) where
  empty = Grammor zeroK
  Grammor rex1 <|> Grammor rex2 = Grammor (rex1 >|< rex2)
  many (Grammor rex) = Grammor (starK rex)
  some (Grammor rex) = Grammor (plusK rex)
instance KleeneStarAlgebra g => Distributor (Grammor g) where
  zeroP = Grammor zeroK
  Grammor rex1 >+< Grammor rex2 = Grammor (rex1 >|< rex2)
  manyP (Grammor rex) = Grammor (starK rex)
  optionalP (Grammor rex) = Grammor (optK rex)
instance KleeneStarAlgebra g => Alternator (Grammor g) where
  alternate = either coerce coerce
  someP (Grammor rex) = Grammor (plusK rex)
instance Tokenized token g => Tokenized token (Grammor g a b) where
  anyToken = Grammor anyToken
  token = Grammor . token
  oneOf = Grammor . oneOf
  notOneOf = Grammor . notOneOf
  asIn = Grammor . asIn
  notAsIn = Grammor . notAsIn
instance TokenAlgebra a g => TokenAlgebra a (Grammor g a b) where
  tokenClass = Grammor . tokenClass
instance TerminalSymbol token g
  => TerminalSymbol token (Grammor g a b) where
  terminal = Grammor . terminal
instance BackusNaurForm g => BackusNaurForm (Grammor g a b) where
  rule name = Grammor . rule name . runGrammor
  ruleRec name = Grammor . ruleRec name . dimap Grammor runGrammor
