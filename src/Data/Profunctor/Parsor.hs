module Data.Profunctor.Parsor
  ( -- *
    Parsor (..)
  , Printor (..)
  , PP (..)
  , pp
  , pParsor
  , pPrintor
--   , Separator (..)
--   , SepBy (..)
--   , Stream1 (..)
--   , Stream (..)
--   , Tokenized (..)
--   , satisfy
--   , Categorized (..)
  ) where

import Control.Applicative
import Control.Category
import Control.Lens
import Control.Lens.Internal.Equator
import Control.Lens.PartialIso
import Control.Monad
import Data.Bifunctor
import Data.Coerce
import Data.List (stripPrefix)
import Data.Profunctor
import Data.Profunctor.Distributor (Distributor (..), Alternator (..), Filtrator (..))
import Data.Profunctor.Monadic
import Data.String
import Prelude hiding ((.), id)
import Witherable

newtype Parsor s t f a b = Parsor {runParsor :: s -> f (b,t)}
newtype Printor s t f a b = Printor {runPrintor :: a -> f (s -> t)}
newtype PP s t f a b = PP {runPP :: s -> f (t, a -> b)}

pp
  :: Applicative f
  => Printor a b f s t
  -> Parsor s t f a b
  -> PP s t f a b
pp (Printor g) (Parsor f) =
  PP (liftA2 (liftA2 (,)) (fmap snd . f) g)

pParsor :: Functor f => PP s t f a b -> a -> Parsor s t f a b
pParsor (PP f) a = Parsor (fmap (\(t, g) -> (g a, t)) . f)

pPrintor :: Functor f => PP s t f a b -> Printor a b f s t
pPrintor (PP f) = Printor (fmap snd . f)

instance Functor f => Functor (Parsor s t f a) where
  fmap f = Parsor . (fmap (first' f) .) . runParsor
instance Functor f => Bifunctor (Parsor s t f) where
  bimap _ = (>>>) coerce . fmap
  first _ = coerce
  second = fmap
instance Functor f => Profunctor (Parsor s t f) where
  dimap _ = (<<<) coerce . fmap
  lmap _ = coerce
  rmap = fmap

instance Monad m => Applicative (Parsor s s m a) where
  pure b = Parsor (\s -> return (b,s))
  Parsor x <*> Parsor y = Parsor $ \s -> do
    (f, t) <- x s
    (a, u) <- y t
    return (f a, u)
instance Monad m => Monad (Parsor s s m a) where
  Parsor p >>= f = Parsor $ \s -> do
    (a, t) <- p s
    runParsor (f a) t
instance (Alternative m, Monad m) => Alternative (Parsor s s m a) where
  empty = Parsor (\_ -> empty)
  Parsor p <|> Parsor q = Parsor (\str -> p str <|> q str)
instance (Alternative m, Monad m) => MonadPlus (Parsor s s m a)
instance (Alternative m, Monad m) => Choice (Parsor s s m) where
  left' = alternate . Left
  right' = alternate . Right
instance (Alternative m, Monad m) => Distributor (Parsor s s m)
instance (Alternative m, Monad m) => Alternator (Parsor s s m) where
  alternate = \case
    Left (Parsor p) -> Parsor (fmap (\(b, str) -> (Left b, str)) . p)
    Right (Parsor p) -> Parsor (fmap (\(b, str) -> (Right b, str)) . p)

instance Filterable f => Filterable (Parsor s t f a) where
  mapMaybe f (Parsor p) = Parsor (mapMaybe (\(a,str) -> (,str) <$> f a) . p)
instance Filterable f => Cochoice (Parsor s t f) where
  unleft = fst . filtrate
  unright = snd . filtrate
instance Filterable f => Filtrator (Parsor s t f) where
  filtrate (Parsor p) =
    ( Parsor (mapMaybe leftMay . p)
    , Parsor (mapMaybe rightMay . p)
    ) where
      leftMay (e, str) = either (\b -> Just (b, str)) (\_ -> Nothing) e
      rightMay (e, str) = either (\_ -> Nothing) (\b -> Just (b, str)) e

instance (Alternative f, Cons s s a a)
  => Equator a a (Parsor s s f) where
    equate = Parsor (\str -> maybe empty pure (uncons str))

instance
  ( Alternative m
  , AsEmpty s, Cons s s Char Char
  , AsEmpty t, Cons t t Char Char
  ) => IsString (Parsor s t m () ()) where
  fromString str = dimapT (review listed) (view listed) $
    Parsor (maybe empty (pure . pure) . stripPrefix str)

instance
  ( Alternative m
  , AsEmpty s, AsEmpty t
  , Cons s s Char Char, Cons t t Char Char
  ) => IsString (Parsor s t m s t) where
  fromString s
    = Parsor
    $ maybe empty (\t -> pure (view listed s, view listed t)) 
    . stripPrefix s
    . review listed

instance Monadic (Parsor s s) where
  joinP (Parsor p) = Parsor $ \s -> do
    (mb, s') <- p s
    b <- mb
    return (b, s')
instance Polyadic Parsor where
  composeP (Parsor p) = Parsor $ \s -> do
    (mb, s') <- p s
    runParsor mb s'
instance Tetradic Parsor where
  dimapT f g (Parsor p) = Parsor (fmap (fmap g) . p . f)

instance Functor f => Functor (Printor s t f a) where
  fmap _ = coerce
instance Functor f => Contravariant (Printor s t f a) where
  contramap _ = coerce
instance Functor f => Profunctor (Printor s t f) where
  dimap f _ = Printor . (. f) . runPrintor
  lmap f = Printor . (. f) . runPrintor
  rmap _ = coerce
instance Tetradic Printor where
  dimapT h i = Printor . (fmap (dimap h i) .) . runPrintor
  tetramap h i f _ = Printor . (fmap (dimap h i) .) . (. f) . runPrintor
