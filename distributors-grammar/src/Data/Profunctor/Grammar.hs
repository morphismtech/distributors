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
  ( -- * Printor
    module Data.Profunctor.Grammar.Printor
    -- * Parsor
  , Parsor (..)
  , unparseP
  , parseP
    -- * Grammor
  , Grammor (..)
  ) where

import Control.Applicative
import Control.Arrow
import Control.Category
import Control.Lens
import Control.Lens.Extras
import Control.Lens.Grammar.BackusNaur
import Control.Lens.Grammar.Machine
import Control.Lens.Grammar.Symbol
import Control.Lens.Grammar.Token
import Control.Monad
import Data.Coerce
import Data.Monoid
import Data.Monoid.Disjunctive
import Data.Profunctor
import Data.Profunctor.Distributor
import Data.Profunctor.Monoidal.Cocartesian
import Data.Profunctor.Filtrator
import Data.Profunctor.Monoidal
import Data.Profunctor.Monadic (MonadicTrans (..))
import Prelude hiding (id, (.))
import GHC.Exts
import Witherable (Filterable (..))
import Data.Profunctor.Grammar.Printor

-- | t'Parsor' is a simple invertible parser `Profunctor`.
newtype Parsor s f a b = Parsor {runParsor :: Maybe a -> s -> f (b,s)}

-- | Run the parser on an input string,
-- `uncons`ing tokens from the beginning of the string,
-- from left to right, returning a value and the remaining string.
parseP :: Parsor s f a b -> s -> f (b,s)
parseP (Parsor f) = f Nothing

-- | Run the parser in reverse on a value and an input string;
-- `snoc`ing tokens at the end of the string, from left to right,
-- and returning the new string.
unparseP :: Functor f => Parsor s f a b -> a -> s -> f s
unparseP (Parsor f) a = fmap snd . f (Just a)

-- | t'Grammor' is a constant `Profunctor`.
newtype Grammor k a b = Grammor {runGrammor :: k}

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
instance MonadicTrans (Parsor s) where
  liftP mb = Parsor (\_ s -> (, s) <$> mb)
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
instance (Alternative m, Monad m) => CocartesianMonoidal (Parsor s m)
{- | `manyP` & `optionalP` parse & print their elements in turn,
rather than through isomorphisms & sums, parsing more before fewer.
-}
instance (Alternative m, Monad m) => Distributor (Parsor s m) where
  manyP (Parsor p) = Parsor $ \ma s -> case ma of
    Nothing -> parsing s
    Just as -> printing as s
    where
      parsing s =
        (do
          (b, s') <- p Nothing s
          (bs, s'') <- parsing s'
          pure (b : bs, s''))
        <|> pure ([], s)
      printing [] s = pure ([], s)
      printing (a : as) s = do
        (b, s') <- p (Just a) s
        (bs, s'') <- printing as s'
        pure (b : bs, s'')
  optionalP (Parsor p) = Parsor $ \ma s -> case ma of
    Nothing -> fmap (first' Just) (p Nothing s) <|> pure (Nothing, s)
    Just Nothing -> pure (Nothing, s)
    Just (Just a) -> fmap (first' Just) (p (Just a) s)
instance (Alternative m, Monad m) => Choice (Parsor s m) where
  left' = alternate . Left
  right' = alternate . Right
instance (Alternative m, Monad m) => DisjunctiveMonoid (Parsor s m a b)
instance (Alternative m, Monad m) => CocartesianChoice (Parsor s m) where
  alternate = \case
    Left (Parsor p) -> Parsor $ \ma s -> case ma of
      Nothing -> fmap (first' Left) (p Nothing s)
      Just (Left a) -> fmap (first' Left) (p (Just a) s)
      Just (Right _) -> empty
    Right (Parsor p) -> Parsor $ \ma s -> case ma of
      Nothing -> fmap (first' Right) (p Nothing s)
      Just (Right a) -> fmap (first' Right) (p (Just a) s)
      Just (Left _) -> empty
instance (Alternative m, Monad m) => Alternator (Parsor s m) where
  optionP def p = Parsor $ \ma s -> case ma of
    Nothing -> runParsor (p <|> pureP def) ma s
    Just _ -> runParsor (pureP def <|> p) ma s
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
  fromString = tokens
instance Ruled (Parsor s m a b)
instance BackusNaurForm (Parsor s m a b)
instance Tried (Parsor s m a b)
instance (Alternative m, Monad m) => MonadFail (Parsor s m a) where
  fail _ = empty
instance AsEmpty s => Matching s (Parsor s [] a b) where
  word =~ p = case
    [ () | (_, remaining) <- runParsor p Nothing word
    , is _Empty remaining
    ] of [] -> False; _:_ -> True

-- Grammor instances
instance Functor (Grammor k a) where fmap _ = coerce
instance Contravariant (Grammor k a) where contramap _ = coerce
instance Profunctor (Grammor k) where dimap _ _ = coerce
instance Bifunctor (Grammor k) where bimap _ _ = coerce
instance Choice (Grammor k) where
  left' = coerce
  right' = coerce
instance Monoid k => Applicative (Grammor k a) where
  pure _ = Grammor mempty
  Grammor rex1 <*> Grammor rex2 = Grammor (rex1 <> rex2)
instance DisjunctiveMonoid k => DisjunctiveMonoid (Grammor k a b) where
  falseP = Grammor falseP
  Grammor rex1 >|< Grammor rex2 = Grammor (rex1 >|< rex2)
instance KleeneStarAlgebra k => Alternative (Grammor k a) where
  empty = falseP
  (<|>) = (>|<)
  many = lmap repeat . manyP
  some = lmap repeat . someP
instance KleeneStarAlgebra k => CocartesianMonoidal (Grammor k)
instance KleeneStarAlgebra k => CocartesianChoice (Grammor k) where
  alternate = either coerce coerce
instance KleeneStarAlgebra k => Distributor (Grammor k) where
  manyP (Grammor rex) = Grammor (starK rex)
  optionalP (Grammor rex) = Grammor (optK rex)
instance KleeneStarAlgebra k => Alternator (Grammor k) where
  someP (Grammor rex) = Grammor (plusK rex)
  optionP _ (Grammor rex) = Grammor (optK rex)
  manyTillP (Grammor rex) (Grammor rest) = Grammor (starK rex <> rest)
  timesP lo hi (Grammor rex) = Grammor (timesK lo hi rex)
instance Tokenized token k => Tokenized token (Grammor k a b) where
  anyToken = Grammor anyToken
  token = Grammor . token
  oneOf = Grammor . oneOf
  notOneOf = Grammor . notOneOf
  asIn = Grammor . asIn
  notAsIn = Grammor . notAsIn
instance TokenAlgebra a k => TokenAlgebra a (Grammor k a b) where
  tokenClass = Grammor . tokenClass
instance TerminalSymbol token k
  => TerminalSymbol token (Grammor k a b) where
  terminal = Grammor . terminal
instance Ruled k => Ruled (Grammor k a b) where
  rule name = Grammor . rule name . runGrammor
instance BackusNaurForm k => BackusNaurForm (Grammor k a b) where
  ruleRec name = Grammor . ruleRec name . dimap Grammor runGrammor
instance Tried k => Tried (Grammor k a b) where
  try = Grammor . try . runGrammor
instance Matching s k => Matching s (Grammor k a b) where
  word =~ pattern = word =~ runGrammor pattern
