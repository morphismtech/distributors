module Data.Profunctor.Grammar
  ( -- * Parsor
    Parsor (..)
  , PP (..)
  , printP
  , parseP
    -- * Printor
  , Printor (..)
  , printor
  , evalPrintor
    -- * Grammor
  , Grammor (..)
    -- * Reador
  , Reador (..)
  , runReador
  , LookT (..)
  , runLookT
  ) where

import Control.Applicative
import Control.Arrow
import Control.Category
import Control.Monad.Codensity
import Control.Monad.Reader
import Control.Monad.State
import Control.Lens
import Control.Lens.Extras
import Control.Lens.Grammar.BackusNaur
import Control.Lens.Grammar.Boole
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

newtype Parsor s f a b = Parsor {runParsor :: s -> f (b,s)}

newtype Printor s f a b = Printor {runPrintor :: a -> f (b, s -> s)}
printor :: Functor f => (a -> f (s -> s)) -> Printor s f a a
printor f = Printor (\a -> fmap (a,) (f a))
evalPrintor :: Functor f => Printor s f a b -> a -> f (s -> s)
evalPrintor (Printor f) = fmap snd . f

newtype PP s f a b = PP {runPP :: Maybe a -> s -> f (b,s)}
printP :: Functor f => PP s f a b -> a -> s -> f s
printP (PP f) a = fmap snd . f (Just a)
parseP :: PP s f a b -> s -> f (b,s)
parseP (PP f) = f Nothing

newtype Grammor t a b = Grammor {runGrammor :: t}

newtype Reador s f a b = Reador {unReador :: Codensity (LookT s f) b}
runReador
  :: (Alternative m, Monad m, IsList s, Cons s s (Item s) (Item s))
  => Reador s m a b -> s -> m (b, s)
runReador (Reador (Codensity f)) = runLookT (f return)

data LookT s f a
  = LookT (s -> LookT s f a)
  | GetT (Item s -> LookT s f a)
  | ResultT a (LookT s f a)
  | FinalT (f (a, s))
runLookT
  :: (Alternative f, IsList s, Cons s s (Item s) (Item s))
  => LookT s f a -> s -> f (a, s)
runLookT (GetT f) s =
  maybe empty (\(h,t) -> runLookT (f h) t) (uncons s)
runLookT (LookT f) s = runLookT (f s) s
runLookT (ResultT x p) s = pure (x,s) <|> runLookT p s
runLookT (FinalT r) _ = r

data LookP s f a b
  = ItemP (a -> f (Item s)) (Item s -> LookP s f a b)
  | LookP (Maybe a -> s -> LookP s f a b)
  | ResultP b (LookP s f a b)
  | FinalP (f (b,s))

runLookP
  :: (Monad m, Alternative m, IsList s, Cons s s (Item s) (Item s))
  => LookP s m a b -> Maybe a -> s -> m (b, s)
runLookP (ItemP f g) ma s = case ma of
  Nothing -> maybe empty
    (\(hd,tl) -> runLookP (g hd) ma tl)
    (uncons s)
  Just a -> do
    item <- f a
    runLookP (g item) ma (cons item s)
runLookP (LookP f) ma s = runLookP (f ma s) ma s
runLookP (ResultP x p) ma s = pure (x,s) <|> runLookP p ma s
runLookP (FinalP r) _ _ = r

-- PP instances
deriving stock instance Functor f => Functor (PP s f a)
instance Functor f => Profunctor (PP s f) where
  dimap f g = PP . dimap (fmap f) (fmap (fmap (first' g))) . runPP
instance Monad m => Applicative (PP s m a) where
  pure b = PP (\_ s -> pure (b,s))
  PP x <*> PP y = PP $ \ma s -> do
    (f, t) <- x ma s
    (a, u) <- y ma t
    return (f a, u)
instance Monad m => Monad (PP s m a) where
  return = pure
  PP p >>= f = PP $ \ma s -> do
    (a, t) <- p ma s
    runPP (f a) ma t
instance (Alternative m, Monad m) => Alternative (PP s m a) where
  empty = PP (\_ _ -> empty)
  PP p <|> PP q = PP $ \ma s -> p ma s <|> q ma s
instance (Alternative m, Monad m) => MonadPlus (PP s m a)
instance Monad m => MonadReader s (PP s m a) where
  ask = PP $ \_ s -> return (s,s)
  local f = PP . fmap (lmap f) . runPP
instance Filterable f => Filterable (PP s f a) where
  mapMaybe f (PP p) = PP $ \fa s ->
    mapMaybe (\(a,t) -> fmap (,t) (f a)) (p fa s)
instance Filterable f => Cochoice (PP s f) where
  unleft = fst . filtrate
  unright = snd . filtrate
instance Filterable f => Filtrator (PP s f) where
  filtrate (PP p) =
    ( PP $ \ma s -> mapMaybe
        (\case{(Left b,t) -> Just (b,t); _ -> Nothing})
        (p (fmap Left ma) s)
    , PP $ \ma s -> mapMaybe
        (\case{(Right b,t) -> Just (b,t); _ -> Nothing})
        (p (fmap Right ma) s)
    )
instance Monad m => Monadic m (PP s) where
  liftP m = PP $ \_ s -> (,s) <$> m
instance (Alternative m, Monad m) => Distributor (PP s m)
instance (Alternative m, Monad m) => Choice (PP s m) where
  left' = alternate . Left
  right' = alternate . Right
instance (Alternative m, Monad m) => Alternator (PP s m) where
  alternate = \case
    Left (PP p) -> PP $ \ma s -> case ma of
      Nothing -> fmap (first' Left) (p Nothing s)
      Just (Left a) -> fmap (first' Left) (p (Just a) s)
      Just (Right _) -> empty
    Right (PP p) -> PP $ \ma s -> case ma of
      Nothing -> fmap (first' Right) (p Nothing s)
      Just (Right a) -> fmap (first' Right) (p (Just a) s)
      Just (Left _) -> empty
instance (Alternative m, Monad m) => Category (PP s m) where
  id = PP $ \ma s -> case ma of
    Nothing -> empty
    Just a  -> pure (a,s)
  PP q . PP p = PP $ \ma s -> case ma of
    Nothing -> empty
    Just a -> do
      (b, t) <- p (Just a) s
      q (Just b) t
instance (Alternative m, Monad m) => Arrow (PP s m) where
  arr f = PP $ \ma s -> case ma of
    Nothing -> empty
    Just a  -> pure (f a, s)
  (***) = (>*<)
instance (Alternative m, Monad m) => ArrowZero (PP s m) where
  zeroArrow = empty
instance (Alternative m, Monad m) => ArrowPlus (PP s m) where
  (<+>) = (<|>)
instance (Alternative m, Monad m) => ArrowChoice (PP s m) where
  (+++) = (>+<)
  left = left'
  right = right'
instance
  ( Categorized a, a ~ Item s, IsList s, Cons s s a a
  , Filterable m, Alternative m, Monad m
  ) => Tokenized a (PP s m a a) where
    anyToken = PP $ maybe
      (maybe empty pure . uncons)
      (\a -> pure . (a,) . cons a)
instance
  ( Categorized a, a ~ Item s, IsList s, Cons s s a a
  , Filterable m, Alternative m, Monad m
  ) => TokenAlgebra a (PP s m a a)
instance
  ( Categorized a, a ~ Item s, IsList s, Cons s s a a
  , Filterable m, Alternative m, Monad m
  ) => TerminalSymbol a (PP s m () ()) where
instance
  ( Char ~ Item s, IsList s, Cons s s Char Char
  , Filterable m, Alternative m, Monad m
  ) => IsString (PP s m () ()) where
  fromString = terminal
instance
  ( Char ~ Item s, IsList s, Cons s s Char Char, AsEmpty s
  , Filterable m, Alternative m, Monad m
  ) => IsString (PP s m s s) where
  fromString = fromTokens
instance BackusNaurForm (PP s m a b)
instance (Alternative m, Monad m) => MonadFail (PP s m a) where
  fail _ = empty

-- Parsor instances
instance Functor f => Functor (Parsor s f a) where
  fmap f = Parsor . fmap (fmap (first' f)) . runParsor
instance Functor f => Bifunctor (Parsor s f) where
  bimap _ = lmap coerce . fmap
  first _ = coerce
  second = fmap
instance Functor f => Profunctor (Parsor s f) where
  dimap _ = rmap coerce . fmap
  lmap _ = coerce
  rmap = fmap
instance Monad m => Applicative (Parsor s m a) where
  pure b = Parsor (\s -> return (b,s))
  Parsor x <*> Parsor y = Parsor $ \s -> do
    (f, t) <- x s
    (a, u) <- y t
    return (f a, u)
instance Monad m => Monad (Parsor s m a) where
  Parsor p >>= f = Parsor $ \s -> do
    (a, t) <- p s
    runParsor (f a) t
instance (Alternative m, Monad m) => Alternative (Parsor s m a) where
  empty = Parsor (\_ -> empty)
  Parsor p <|> Parsor q = Parsor (\str -> p str <|> q str)
instance (Alternative m, Monad m) => MonadPlus (Parsor s m a)
instance Monad m => MonadState s (Parsor s m a) where
  get = Parsor (\s -> pure (s,s))
  put = Parsor . (pure (pure . ((),)))
instance (Alternative m, Monad m) => Choice (Parsor s m) where
  left' = alternate . Left
  right' = alternate . Right
instance (Alternative m, Monad m) => Distributor (Parsor s m)
instance (Alternative m, Monad m) => Alternator (Parsor s m) where
  alternate = \case
    Left (Parsor p) -> Parsor (fmap (\(b, str) -> (Left b, str)) . p)
    Right (Parsor p) -> Parsor (fmap (\(b, str) -> (Right b, str)) . p)
instance Monad m => Monadic m (Parsor s) where
  liftP m = Parsor $ \s -> (,s) <$> m
instance Filterable f => Filterable (Parsor s f a) where
  mapMaybe f (Parsor p) = Parsor (mapMaybe (\(a,str) -> (,str) <$> f a) . p)
instance Filterable f => Cochoice (Parsor s f) where
  unleft = fst . filtrate
  unright = snd . filtrate
instance Filterable f => Filtrator (Parsor s f) where
  filtrate (Parsor p) =
    ( Parsor (mapMaybe leftMay . p)
    , Parsor (mapMaybe rightMay . p)
    ) where
      leftMay (e, str) = either (\b -> Just (b, str)) (\_ -> Nothing) e
      rightMay (e, str) = either (\_ -> Nothing) (\b -> Just (b, str)) e
instance
  ( Categorized a, a ~ Item s, IsList s, Cons s s a a
  , Filterable m, Alternative m, Monad m
  ) => Tokenized a (Parsor s m a a) where
  anyToken = Parsor (maybe empty pure . uncons)
instance
  ( Categorized a, a ~ Item s, IsList s, Cons s s a a
  , Filterable m, Alternative m, Monad m
  ) => TokenAlgebra a (Parsor s m a a)
instance
  ( Categorized a, a ~ Item s, IsList s, Cons s s a a
  , Filterable m, Alternative m, Monad m
  ) => TerminalSymbol a (Parsor s m () ())
instance
  ( Char ~ Item s, IsList s, Cons s s Char Char
  , Filterable m, Alternative m, Monad m
  ) => IsString (Parsor s m () ()) where
  fromString = terminal
instance
  ( Char ~ Item s, IsList s, Cons s s Char Char, AsEmpty s
  , Filterable m, Alternative m, Monad m
  ) => IsString (Parsor s m s s) where
  fromString = fromTokens
instance BackusNaurForm (Parsor s m a b)
instance AsEmpty s => Matching s (Parsor s Maybe a b) where
  word =~ parsor = case runParsor parsor word of
    Nothing -> False
    Just (_,t) -> is _Empty t
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
instance Monad m => MonadReader a (Printor s m a) where
  ask = Printor (\a -> return (a, id))
  reader f = (Printor (\a -> return (f a, id)))
  local f = Printor . (\m -> m . f) . runPrintor
instance Monad m => Monadic m (Printor s) where
  liftP m = Printor $ \_ -> (, id) <$> m
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
instance Functor (Grammor t a) where fmap _ = coerce
instance Contravariant (Grammor t a) where contramap _ = coerce
instance Profunctor (Grammor t) where dimap _ _ = coerce
instance Bifunctor (Grammor t) where bimap _ _ = coerce
instance Choice (Grammor t) where
  left' = coerce
  right' = coerce
instance Monoid t => Applicative (Grammor t a) where
  pure _ = Grammor mempty
  Grammor rex1 <*> Grammor rex2 = Grammor (rex1 <> rex2)
instance KleeneStarAlgebra t => Alternative (Grammor t a) where
  empty = Grammor zeroK
  Grammor rex1 <|> Grammor rex2 = Grammor (rex1 >|< rex2)
  many (Grammor rex) = Grammor (starK rex)
  some (Grammor rex) = Grammor (plusK rex)
instance KleeneStarAlgebra t => Distributor (Grammor t) where
  zeroP = Grammor zeroK
  Grammor rex1 >+< Grammor rex2 = Grammor (rex1 >|< rex2)
  manyP (Grammor rex) = Grammor (starK rex)
  optionalP (Grammor rex) = Grammor (optK rex)
instance KleeneStarAlgebra t => Alternator (Grammor t) where
  alternate = either coerce coerce
  someP (Grammor rex) = Grammor (plusK rex)
instance Tokenized token t => Tokenized token (Grammor t a b) where
  anyToken = Grammor anyToken
  token = Grammor . token
  oneOf = Grammor . oneOf
  notOneOf = Grammor . notOneOf
  asIn = Grammor . asIn
  notAsIn = Grammor . notAsIn
instance TokenAlgebra a t => TokenAlgebra a (Grammor t a b) where
  tokenClass = Grammor . tokenClass
instance TerminalSymbol token t
  => TerminalSymbol token (Grammor t a b) where
  terminal = Grammor . terminal
instance BackusNaurForm t => BackusNaurForm (Grammor t a b) where
  rule name = Grammor . rule name . runGrammor
  ruleRec name = Grammor . ruleRec name . dimap Grammor runGrammor

-- Reador instances
deriving newtype instance Functor (Reador s f a)
deriving newtype instance Applicative (Reador s f a)
deriving newtype instance Monad (Reador s f a)
deriving newtype instance (Alternative m, Monad m, IsList s, Cons s s (Item s) (Item s))
  => Alternative (Reador s m a)
deriving newtype instance (Alternative m, Monad m, IsList s, Cons s s (Item s) (Item s))
  => MonadPlus (Reador s m a)
instance (Alternative m, Filterable m, Monad m, IsList s, Cons s s (Item s) (Item s))
  => Filterable (Reador s m a) where
  mapMaybe f
    = Reador . lift
    . mapMaybe f
    . lowerCodensity . unReador
instance Profunctor (Reador s f) where
  dimap _ f (Reador p) = Reador (fmap f p)
instance Bifunctor (Reador s f) where
  bimap _ f (Reador p) = Reador (fmap f p)
instance (Alternative m, Monad m, IsList s, Cons s s (Item s) (Item s))
  => Monadic m (Reador s) where
  liftP m = Reador $ do
    s <- ask
    lift $ FinalT ((,s) <$> m)
instance (Alternative m, Monad m, IsList s, Cons s s (Item s) (Item s))
  => Choice (Reador s m) where
  left' = alternate . Left
  right' = alternate . Right
instance (Alternative m, Monad m, Filterable m, IsList s, Cons s s (Item s) (Item s))
  => Cochoice (Reador s m) where
  unleft = fst . filtrate
  unright = snd . filtrate
instance (Alternative m, Monad m, IsList s, Cons s s (Item s) (Item s))
  => Distributor (Reador s m)
instance (Alternative m, Monad m, IsList s, Cons s s (Item s) (Item s))
  => Alternator (Reador s m) where
  alternate (Left (Reador p)) = Reador (fmap Left p)
  alternate (Right (Reador p)) = Reador (fmap Right p)
instance (Alternative m, Filterable m, Monad m, IsList s, Cons s s (Item s) (Item s))
  => Filtrator (Reador s m) where
  filtrate = mfiltrate
instance
  ( Alternative m, Filterable m, Monad m
  , IsList s, Categorized c, c ~ Item s, Cons s s c c
  ) => Tokenized c (Reador s m c c) where
  anyToken = Reador (lift (GetT return))
instance
  ( Filterable m, Alternative m, Monad m
  , IsList s, Categorized c, c ~ Item s, Cons s s c c
  ) => TokenAlgebra c (Reador s m c c)
instance
  ( Filterable m, Alternative m, Monad m
  , IsList s, Categorized c, c ~ Item s, Cons s s c c
  ) => TerminalSymbol c (Reador s m () ())
instance
  ( Filterable m, Alternative m, Monad m
  , IsList s, Item s ~ Char, Cons s s Char Char
  ) => IsString (Reador s m () ()) where
  fromString = terminal
instance
  ( Filterable m, Alternative m, Monad m
  , IsList s, Item s ~ Char, AsEmpty s, Cons s s Char Char
  ) => IsString (Reador s m s s) where
  fromString = fromTokens
instance BackusNaurForm (Reador s m a b)
instance (IsList s, Cons s s (Item s) (Item s), AsEmpty s)
  => Matching s (Reador s Maybe a b) where
  word =~ reador = case runReador reador word of
    Nothing -> False
    Just (_,t) -> is _Empty t
instance
  ( Alternative m, Monad m
  , IsList s, Item s ~ Char, Cons s s Char Char
  ) => MonadFail (Reador s m a) where
  fail _ = empty

-- LookT instances
deriving stock instance Functor f => Functor (LookT s f)
instance (Alternative m, Monad m, IsList s, Cons s s (Item s) (Item s))
  => Applicative (LookT s m) where
  pure x = ResultT x (FinalT empty)
  (<*>) = ap
instance (Alternative m, Monad m, IsList s, Cons s s (Item s) (Item s))
  => Monad (LookT s m) where
  GetT f >>= k = GetT $ \c -> f c >>= k
  LookT f >>= k = LookT $ \s -> f s >>= k
  ResultT x p >>= k = k x <|> (p >>= k)
  FinalT r >>= k = FinalT $ do
    (x,s) <- r
    runLookT (k x) s
instance (Alternative m, Monad m, IsList s, Cons s s (Item s) (Item s))
  => MonadReader s (LookT s m) where
  ask = LookT return
  local f = \case
    GetT k -> do
      s <- ask
      FinalT (runLookT (GetT k) (f s))
    LookT k -> LookT (k . f)
    ResultT x p -> ResultT x (local f p)
    FinalT r -> FinalT r
instance Filterable f => Filterable (LookT s f) where
  mapMaybe f = \case
    GetT k -> GetT (mapMaybe f . k)
    LookT k -> LookT (mapMaybe f . k)
    ResultT x p -> mapMaybe f p & case f x of
      Nothing -> id
      Just y -> ResultT y
    FinalT r -> FinalT (mapMaybe (\(a,s) -> (,s) <$> f a) r)
instance (Alternative m, Monad m, IsList s, Cons s s (Item s) (Item s))
  => Alternative (LookT s m) where
  empty = FinalT empty
  -- most common case: two gets are combined
  GetT f1 <|> GetT f2 = GetT (\c -> f1 c <|> f2 c)
  -- results are delivered as soon as possible
  ResultT x p <|> q = ResultT x (p <|> q)
  p <|> ResultT x q = ResultT x (p <|> q)
  -- two finals are combined
  -- final + look becomes one look and one final (=optimization)
  -- final + sthg else becomes one look and one final
  FinalT r <|> FinalT t = FinalT (r <|> t)
  FinalT r <|> LookT f = LookT $ \s -> FinalT (r <|> runLookT (f s) s)
  FinalT r <|> p = LookT $ \s -> FinalT (r <|> runLookT p s)
  LookT f <|> FinalT r = LookT $ \s -> FinalT (runLookT (f s) s <|> r)
  p <|> FinalT r = LookT $ \s -> FinalT (runLookT p s <|> r)
  -- two looks are combined (=optimization)
  -- look + sthg else floats upwards
  LookT f <|> LookT g = LookT (\s -> f s <|> g s)
  LookT f <|> p = LookT (\s -> f s <|> p)
  p <|> LookT f = LookT (\s -> p <|> f s)

-- LookP instances
deriving stock instance Functor f => Functor (LookP s f a)
instance Functor f => Profunctor (LookP s f) where
  dimap f g = \case
    ItemP l k -> ItemP (lmap f l) (rmap (dimap f g) k)
    LookP k -> LookP (dimap (fmap f) (rmap (dimap f g)) k)
    ResultP c p -> ResultP (g c) (dimap f g p)
    FinalP r -> FinalP (fmap (first' g) r)
instance (Alternative m, Monad m, IsList s, Cons s s (Item s) (Item s))
  => Applicative (LookP s m a) where
  pure x = ResultP x (FinalP empty)
  (<*>) = ap
instance (Alternative m, Monad m, IsList s, Cons s s (Item s) (Item s))
  => Monad (LookP s m a) where
  ItemP f g >>= k = ItemP f $ \c -> g c >>= k
  LookP f >>= k = LookP $ \ma s -> f ma s >>= k
  ResultP x p >>= k = k x <|> (p >>= k)
  FinalP r >>= k = FinalP $ do
    (x,s) <- r
    runLookP (k x) Nothing s
instance (Alternative m, Monad m, IsList s, Cons s s (Item s) (Item s))
  => Monadic m (LookP s) where
  liftP m = do
    s <- LookP (\_ -> return)
    FinalP $ (,s) <$> m
instance Filterable f => Filterable (LookP s f a) where
  mapMaybe f = \case
    ItemP l k -> ItemP l (mapMaybe f . k)
    LookP k -> LookP (\ma -> mapMaybe f . k ma)
    ResultP x p -> mapMaybe f p & case f x of
      Nothing -> id
      Just y -> ResultP y
    FinalP r -> FinalP (mapMaybe (\(a,s) -> (,s) <$> f a) r)
instance Filterable f => Cochoice (LookP s f) where
  unleft = fst . filtrate
  unright = snd . filtrate
instance Filterable f => Filtrator (LookP s f) where
  filtrate = \case
    ItemP l k ->
      ( ItemP (l . Left) (fst . filtrate . k)
      , ItemP (l . Right) (snd . filtrate . k)
      )
    LookP k ->
      ( LookP (dimap (fmap Left) (rmap (fst . filtrate)) k)
      , LookP (dimap (fmap Right) (rmap (snd . filtrate)) k)
      )
    ResultP x p -> case x of
      Left b ->
        ( ResultP b (fst (filtrate p))
        , snd (filtrate p)
        )
      Right c ->
        ( fst (filtrate p)
        , ResultP c (snd (filtrate p))
        )
    FinalP r ->
      ( FinalP (mapMaybe (\case {(Left b, s) -> Just (b,s); _ -> Nothing}) r)
      , FinalP (mapMaybe (\case {(Right c, s) -> Just (c,s); _ -> Nothing}) r)
      )
instance (Alternative m, Monad m, IsList s, Cons s s (Item s) (Item s))
  => Alternative (LookP s m a) where
  empty = FinalP empty
  -- most common case: two items are combined
  ItemP l1 f1 <|> ItemP l2 f2 =
    ItemP (\a -> l1 a <|> l2 a) (\c -> f1 c <|> f2 c)
  -- results are delivered as soon as possible
  ResultP x p <|> q = ResultP x (p <|> q)
  p <|> ResultP x q = ResultP x (p <|> q)
  -- two finals are combined
  -- final + look becomes one look and one final (=optimization)
  -- final + sthg else becomes one look and one final
  FinalP r <|> FinalP t = FinalP (r <|> t)
  FinalP r <|> LookP f = LookP $ \ma s -> FinalP (r <|> runLookP (f ma s) ma s)
  FinalP r <|> p = LookP $ \ma s -> FinalP (r <|> runLookP p ma s)
  LookP f <|> FinalP r = LookP $ \ma s -> FinalP (runLookP (f ma s) ma s <|> r)
  p <|> FinalP r = LookP $ \ma s -> FinalP (runLookP p ma s <|> r)
  -- two looks are combined (=optimization)
  -- look + sthg else floats upwards
  LookP f <|> LookP g = LookP (\ma s -> f ma s <|> g ma s)
  LookP f <|> p = LookP (\ma s -> f ma s <|> p)
  p <|> LookP f = LookP (\ma s -> p <|> f ma s)
instance (Alternative m, Monad m, IsList s, Cons s s (Item s) (Item s))
  => Choice (LookP s m) where
  left' = alternate . Left
  right' = alternate . Right
instance (Alternative m, Monad m, IsList s, Cons s s (Item s) (Item s))
  => Alternator (LookP s m) where
  alternate = \case
    Left (ItemP l k) ->
      ItemP (either l (const empty)) (alternate . Left . k)
    Right (ItemP l k) ->
      ItemP (either (const empty) l) (alternate . Right . k)
    Left (LookP k) -> LookP $ dimap
      (maybe Nothing (either Just (const Nothing)))
      (rmap (alternate . Left)) k
    Right (LookP k) -> LookP $ dimap
      (maybe Nothing (either (const Nothing) Just))
      (rmap (alternate . Right)) k
    Left (ResultP x p) -> ResultP (Left x) (alternate (Left p))
    Right (ResultP x p) -> ResultP (Right x) (alternate (Right p))
    Left (FinalP r) -> FinalP (fmap (first' Left) r)
    Right (FinalP r) -> FinalP (fmap (first' Right) r)
instance (Alternative m, Monad m, IsList s, Cons s s (Item s) (Item s))
  => Distributor (LookP s m)
