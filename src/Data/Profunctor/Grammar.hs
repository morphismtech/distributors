module Data.Profunctor.Grammar
  ( -- * Parsor
    Parsor (..)
    -- * Printor
  , Printor (..)
  , printor
  , evalPrintor
    -- * Grammor
  , Grammor (..)
  , grammor
  , evalGrammor
  , evalGrammor_
  ) where

import Control.Applicative
import Control.Arrow
import Control.Category
import Control.Comonad
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Lens
import Control.Lens.Extras
import Control.Lens.Internal.Equator
import Control.Lens.Grammar.BackusNaur
import Control.Lens.Grammar.Kleene
import Control.Lens.Grammar.Symbol
import Control.Lens.Grammar.Token
import Control.Monad
import Data.Bifunctor
import Data.Coerce
import Data.Monoid
import Data.Profunctor
import Data.Profunctor.Distributor
import Data.Profunctor.Filtrator
import Data.Profunctor.Monadic
import Data.Profunctor.Monoidal
import Data.Void
import Prelude hiding (id, (.))
import GHC.Exts
import Witherable

newtype Parsor s t f a b = Parsor {runParsor :: s -> f (b,t)}

newtype Printor s t f a b = Printor {runPrintor :: a -> f (b, s -> t)}
printor :: Functor f => (a -> f (s -> t)) -> Printor s t f a a
printor f = Printor (\a -> fmap (a,) (f a))
evalPrintor :: Functor f => Printor s t f a b -> a -> f (s -> t)
evalPrintor (Printor f) = fmap snd . f

newtype Grammor s t f a b = Grammor {runGrammor :: s -> f t}
grammor :: Applicative f => t -> Grammor s t f a b
grammor = Grammor . pure . pure
evalGrammor :: (Monoid s, Comonad f) => Grammor s t f a b -> t
evalGrammor = extract . extract . runGrammor
evalGrammor_ :: Grammor () t Identity a b -> t
evalGrammor_ = evalGrammor

-- Parsor instances
instance Functor f => Functor (Parsor s t f a) where
  fmap f = Parsor . fmap (fmap (first' f)) . runParsor
instance Functor f => Bifunctor (Parsor s t f) where
  bimap _ = lmap coerce . fmap
  first _ = coerce
  second = fmap
instance Functor f => Profunctor (Parsor s t f) where
  dimap _ = rmap coerce . fmap
  lmap _ = coerce
  rmap = fmap
instance Functor f => Tetradic f Parsor where
  dimapT f g (Parsor p) = Parsor (fmap (fmap g) . p . f)
  tetramap f g _ i (Parsor p) = Parsor (fmap (i >*< g) . p . f)
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
instance MonadError e m => MonadError e (Parsor s s m a) where
  throwError = liftP . throwError
  catchError p f = Parsor $ \s ->
    catchError (runParsor p s) (\e -> runParsor (f e) s)
instance Monad m => MonadState s (Parsor s s m a) where
  get = Parsor (\s -> pure (s,s))
  put = Parsor . (pure (pure . ((),)))
instance (Alternative m, Monad m) => Choice (Parsor s s m) where
  left' = alternate . Left
  right' = alternate . Right
instance (Alternative m, Monad m) => Distributor (Parsor s s m)
instance (Alternative m, Monad m) => Alternator (Parsor s s m) where
  alternate = \case
    Left (Parsor p) -> Parsor (fmap (\(b, str) -> (Left b, str)) . p)
    Right (Parsor p) -> Parsor (fmap (\(b, str) -> (Right b, str)) . p)
instance Monad m => Monadic m (Parsor s s) where
  joinP (Parsor p) = Parsor $ \s -> do
    (mb, s') <- p s
    b <- mb
    return (b, s')
instance Monad m => Polyadic m Parsor where
  composeP (Parsor p) = Parsor $ \s -> do
    (mb, s') <- p s
    runParsor mb s'
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
instance
  ( Categorized a, a ~ Item s, IsList s, Cons s s a a
  , Filterable m, Alternative m, Monad m
  ) => Tokenized a (Parsor s s m a a) where
  anyToken = Parsor (maybe empty pure . uncons)
instance
  ( Categorized a, a ~ Item s, IsList s, Cons s s a a
  , Filterable m, Alternative m, Monad m
  ) => TestAlgebra (TokenTest a) (Parsor s s m a a)
instance
  ( Categorized a, a ~ Item s, IsList s, Cons s s a a
  , Filterable m, Alternative m, Monad m
  ) => Equator a a (Parsor s s m)
instance
  ( Categorized a, a ~ Item s, IsList s, Cons s s a a
  , Filterable m, Alternative m, Monad m
  ) => TerminalSymbol a (Parsor s s m () ())
instance
  ( Char ~ Item s, IsList s, Cons s s Char Char
  , Filterable m, Alternative m, Monad m
  ) => IsString (Parsor s s m () ()) where
  fromString = terminal
instance
  ( Char ~ Item s, IsList s, Cons s s Char Char, AsEmpty s
  , Filterable m, Alternative m, Monad m
  ) => IsString (Parsor s s m s s) where
  fromString = fromTokens
instance BackusNaurForm (Parsor s t m a b)
instance AsEmpty t => Matching s (Parsor s t Maybe a b) where
  word =~ parsor = case runParsor parsor word of
    Nothing -> False
    Just (_,t) -> is _Empty t

-- Printor instances
instance Functor f => Functor (Printor s t f a) where
  fmap f = Printor . fmap (fmap (first' f)) . runPrintor
instance Functor f => Profunctor (Printor s t f) where
  dimap f g = Printor . dimap f (fmap (first' g)) . runPrintor
instance Functor f => Tetradic f Printor where
  dimapT f g = Printor . rmap (fmap (second' (dimap f g))) . runPrintor
  tetramap f g h i = Printor . dimap h (fmap (i >*< dimap f g)) . runPrintor
instance Applicative f => Applicative (Printor s s f a) where
  pure b = Printor (\_ -> pure (b, id))
  Printor f <*> Printor x = Printor $ \c ->
    liftA2 (\(g, p) (a, q) -> (g a, p . q)) (f c) (x c)
instance Alternative f => Alternative (Printor s s f a) where
  empty = Printor (\_ -> empty)
  Printor p <|> Printor q = Printor (\a -> p a <|> q a)
instance Filterable f => Filterable (Printor s s f a) where
  mapMaybe f (Printor p) = Printor $
    mapMaybe (\(a,q) -> fmap (, q) (f a)) . p
instance Monad f => Monad (Printor s s f a) where
  return = pure
  mx >>= f = composeP (fmap f mx)
instance (Alternative f, Monad f) => MonadPlus (Printor s s f a)
instance MonadError e m => MonadError e (Printor s s m a) where
  throwError = liftP . throwError
  catchError p f = Printor $ \s ->
    catchError (runPrintor p s) (\e -> runPrintor (f e) s)
instance Monad m => MonadReader a (Printor s s m a) where
  ask = Printor (\a -> return (a, id))
  reader f = (Printor (\a -> return (f a, id)))
  local f = Printor . (\m -> m . f) . runPrintor
instance Monad m => Monadic m (Printor s s) where
  joinP (Printor mf) = Printor $ \a -> do
    (mb, f) <- mf a
    b <- mb
    return (b, f)
instance Monad m => Polyadic m Printor where
  composeP (Printor mf) = Printor $ \a -> do
    (Printor mg, f) <- mf a
    (b, g) <- mg a
    return (b, g . f)
instance Applicative f => Distributor (Printor s s f) where
  zeroP = Printor absurd
  Printor p >+< Printor q = Printor $
    either (fmap (first' Left) . p) (fmap (first' Right) . q)
instance Alternative f => Alternator (Printor s s f) where
  alternate = \case
    Left (Printor p) -> Printor $
      either (fmap (first' Left) . p) (\_ -> empty)
    Right (Printor p) -> Printor $
      either (\_ -> empty) (fmap (first' Right) . p)
instance Filterable f => Filtrator (Printor s s f) where
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
instance Alternative f => Choice (Printor s s f) where
  left' = alternate . Left
  right' = alternate . Right
instance Filterable f => Cochoice (Printor s s f) where
  unleft = fst . filtrate
  unright = snd . filtrate
instance Functor f => Strong (Printor s s f) where
  first' (Printor p) =
    Printor (\(a,c) -> fmap (\(b,q) -> ((b,c),q)) (p a))
  second' (Printor p) =
    Printor (\(c,a) -> fmap (\(b,q) -> ((c,b),q)) (p a))
instance Monad f => Category (Printor s s f) where
  id = Printor $ \a -> return (a, id)
  Printor q . Printor p = Printor $ \a -> do
    (b, p') <- p a
    (c, q') <- q b
    return (c, q' . p')
instance Monad f => Arrow (Printor s s f) where
  arr f = Printor (return . (, id) . f)
  (***) = (>*<)
  first = first'
  second = second'
instance (Alternative f, Monad f) => ArrowZero (Printor s s f) where
  zeroArrow = empty
instance (Alternative f, Monad f) => ArrowPlus (Printor s s f) where
  (<+>) = (<|>)
instance (Alternative f, Monad f) => ArrowChoice (Printor s s f) where
  (+++) = (>+<)
  left = left'
  right = right'
instance
  ( Categorized a, a ~ Item s, IsList s, Cons s s a a
  , Filterable m, Alternative m, Monad m
  ) => Tokenized a (Printor s s m a a) where
  anyToken = Printor (\b -> pure (b, cons b))
instance
  ( Categorized a, a ~ Item s, IsList s, Cons s s a a
  , Filterable m, Alternative m, Monad m
  ) => TestAlgebra (TokenTest a) (Printor s s m a a)
instance
  ( Categorized a, a ~ Item s, IsList s, Cons s s a a
  , Filterable m, Alternative m, Monad m
  ) => Equator a a (Printor s s m)
instance 
  ( Categorized a, a ~ Item s, IsList s, Cons s s a a
  , Filterable m, Alternative m, Monad m
  ) => TerminalSymbol a (Printor s s m () ()) where
instance
  ( Char ~ Item s, IsList s, Cons s s Char Char
  , Filterable m, Alternative m, Monad m
  ) => IsString (Printor s s m () ()) where
  fromString = terminal
instance
  ( Char ~ Item s, IsList s, Cons s s Char Char, AsEmpty s
  , Filterable m, Alternative m, Monad m
  ) => IsString (Printor s s m s s) where
  fromString = fromTokens
instance BackusNaurForm (Printor s t m a b)

-- Grammor instances
instance Functor (Grammor s t f a) where fmap _ = coerce
instance Contravariant (Grammor s t f a) where contramap _ = coerce
instance Profunctor (Grammor s t f) where dimap _ _ = coerce
instance Bifunctor (Grammor s t f) where bimap _ _ = coerce
instance Functor f => Tetradic f Grammor where
  dimapT f g = Grammor . dimap f (fmap g) . runGrammor
  tetramap f g _ _ = Grammor . dimap f (fmap g) . runGrammor
instance Choice (Grammor s t f) where
  left' = coerce
  right' = coerce
instance Filterable (Grammor s t ((,) All) a) where
  mapMaybe _ = Grammor . fmap (\(_, t) -> (All False, t)) . runGrammor
instance Cochoice (Grammor s t ((,) All)) where
  unleft = Grammor . fmap (\(_, t) -> (All False, t)) . runGrammor
  unright = Grammor . fmap (\(_, t) -> (All False, t)) . runGrammor
instance Filtrator (Grammor s t ((,) All)) where
  filtrate (Grammor p) =
    ( Grammor (fmap (\(_, t) -> (All False, t)) p)
    , Grammor (fmap (\(_, t) -> (All False, t)) p)
    )
instance (Monoid t, Applicative f)
  => Applicative (Grammor s t f a) where
  pure _ = Grammor (pure (pure mempty))
  Grammor rex1 <*> Grammor rex2 =
    Grammor (liftA2 (liftA2 (<>)) rex1 rex2)
instance (KleeneStarAlgebra t, Applicative f)
  => Alternative (Grammor s t f a) where
  empty = Grammor (pure (pure zeroK))
  Grammor rex1 <|> Grammor rex2 =
    Grammor (liftA2 (liftA2 (>|<)) rex1 rex2)
  many (Grammor rex) = Grammor (fmap (fmap starK) rex)
  some (Grammor rex) = Grammor (fmap (fmap plusK) rex)
instance (KleeneStarAlgebra t, Applicative f)
  => Distributor (Grammor s t f) where
  zeroP = Grammor (pure (pure zeroK))
  Grammor rex1 >+< Grammor rex2 =
    Grammor (liftA2 (liftA2 (>|<)) rex1 rex2)
  manyP (Grammor rex) = Grammor (fmap (fmap starK) rex)
  optionalP (Grammor rex) = Grammor (fmap (fmap optK) rex)
instance (KleeneStarAlgebra t, Applicative f)
  => Alternator (Grammor s t f) where
  alternate = either coerce coerce
  someP (Grammor rex) = Grammor (fmap (fmap plusK) rex)
instance (Tokenized token t, Applicative f)
  => Tokenized token (Grammor s t f a b) where
  anyToken = grammor anyToken
  token = grammor . token
  oneOf = grammor . oneOf
  notOneOf = grammor . notOneOf
  asIn = grammor . asIn
  notAsIn = grammor . notAsIn
instance (TestAlgebra bool t, Applicative f)
  => TestAlgebra bool (Grammor s t f a b) where
  testB = grammor . testB
instance (TerminalSymbol token t, Applicative f)
  => TerminalSymbol token (Grammor s t f a b) where
  terminal = grammor . terminal
instance (Comonad f, Applicative f, Monoid s, BackusNaurForm t)
  => BackusNaurForm (Grammor s t f a b) where
  rule name = Grammor . fmap (fmap (rule name)) . runGrammor
  ruleRec name = grammor . ruleRec name . dimap grammor evalGrammor
