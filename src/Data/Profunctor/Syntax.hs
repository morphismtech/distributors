module Data.Profunctor.Syntax
  ( InvariantP (..)
  , Parsor (..)
  , Printor (..)
  , Lintor (..)
  , SyntaxP (..)
  , toPrintor
  , fromPrintor
  , Subtextual
  ) where

import Control.Applicative
import Control.Arrow
import Control.Category
import Control.Lens
import Control.Lens.Internal.Equator
import Control.Lens.RegEx
import Control.Lens.Stream
import Control.Lens.Token
import Control.Monad
import Data.Bifunctor
import Data.Coerce
import Data.Monoid
import Data.Profunctor
import Data.Profunctor.Distributor
import Data.Profunctor.Monadic
import Data.Void
import Prelude hiding (id, (.))
import GHC.Exts
import Witherable

newtype InvariantP r a b = InvariantP {runInvariantP :: r}
newtype Parsor s t f a b = Parsor {runParsor :: s -> f (b,t)}
newtype Printor s t f a b = Printor {runPrintor :: a -> f (s -> t)}
newtype Lintor s t f a b = Lintor {runLintor :: a -> f (b, s -> t)}
newtype SyntaxP s t f a b = SyntaxP {runSyntaxP :: f t}

toPrintor :: Functor f => Lintor s t f a b -> Printor s t f a b
toPrintor (Lintor f) = Printor (fmap snd . f)

fromPrintor :: Functor f => Printor s t f a a -> Lintor s t f a a
fromPrintor (Printor f) = Lintor (\a -> fmap (a,) (f a))

type Subtextual s m =
  ( IsStream s, Categorized (Item s)
  , Alternative m, Filterable m, Monad m
  )

instance Functor (InvariantP r a) where fmap _ = coerce
instance Contravariant (InvariantP r a) where contramap _ = coerce
instance Profunctor (InvariantP r) where dimap _ _ = coerce
instance Bifunctor (InvariantP r) where bimap _ _ = coerce
instance Choice (InvariantP r) where
  left' = coerce
  right' = coerce
subsetOf
  :: InvariantP (rules, (All, start)) a b
  -> InvariantP (rules, (All, start)) s t
subsetOf (InvariantP (rules, (_, start))) =
  InvariantP (rules, ((All False), start))
instance Filterable (InvariantP (rules, (All, start)) x) where
  mapMaybe _ = subsetOf
instance Cochoice (InvariantP (rules, (All, start))) where
  unleft = subsetOf
instance Filtrator (InvariantP (rules, (All, start))) where
  filtrate p = (subsetOf p, subsetOf p)
instance Monoid r => Applicative (InvariantP r a) where
  pure _ = InvariantP mempty
  InvariantP rex1 <*> InvariantP rex2 =
    InvariantP (rex1 <> rex2)
instance KleeneStarAlgebra r => Alternative (InvariantP r a) where
  empty = InvariantP failK
  InvariantP rex1 <|> InvariantP rex2 =
    InvariantP (rex1 `altK` rex2)
  many (InvariantP rex) = InvariantP (starK rex)
  some (InvariantP rex) = InvariantP (plusK rex)
instance KleeneStarAlgebra r => Distributor (InvariantP r) where
  zeroP = InvariantP failK
  InvariantP rex1 >+< InvariantP rex2 =
    InvariantP (rex1 `altK` rex2)
  manyP (InvariantP rex) = InvariantP (starK rex)
  optionalP (InvariantP rex) = InvariantP (optK rex)
instance KleeneStarAlgebra r => Alternator (InvariantP r) where
  alternate = either coerce coerce
  someP (InvariantP rex) = InvariantP (plusK rex)
instance (Tokenized r, Categorized c, Token r ~ c)
  => Tokenized (InvariantP r c c) where
  type Token (InvariantP r c c) = Token r
  anyToken = InvariantP anyToken
  token = InvariantP . token
  inClass = InvariantP . inClass
  notInClass = InvariantP . notInClass
  inCategory = InvariantP . inCategory
  notInCategory = InvariantP . notInCategory
instance TerminalSymbol (InvariantP (RegEx c) () ()) where
  type Alphabet (InvariantP (RegEx c) () ()) = c
  terminal = InvariantP . terminal
instance
  ( Monoid a
  , TerminalSymbol b
  ) => TerminalSymbol (InvariantP (a,b) () ()) where
  type Alphabet (InvariantP (a,b) () ()) = Alphabet b
  terminal = InvariantP . pure . terminal

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
instance (Alternative m, Monad m) => Choice (Parsor s s m) where
  left' = alternate . Left
  right' = alternate . Right
instance (Alternative m, Monad m) => Distributor (Parsor s s m)
instance (Alternative m, Monad m) => Alternator (Parsor s s m) where
  alternate = \case
    Left (Parsor p) -> Parsor (fmap (\(b, str) -> (Left b, str)) . p)
    Right (Parsor p) -> Parsor (fmap (\(b, str) -> (Right b, str)) . p)
instance Monadic (Parsor s s) where
  joinP (Parsor p) = Parsor $ \s -> do
    (mb, s') <- p s
    b <- mb
    return (b, s')
instance Polyadic Parsor where
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

instance (Subtextual s m, a ~ Item s) => Tokenized (Parsor s s m a a) where
  type Token (Parsor s s m a a) = a
  anyToken = Parsor (\str -> maybe empty pure (uncons str))
instance (Subtextual s m, a ~ Item s) => Equator a a (Parsor s s m) where
  equate = anyToken
instance Subtextual s m => TerminalSymbol (Parsor s s m () ()) where
  type Alphabet (Parsor s s m () ()) = Item s
instance (Subtextual s m, Item s ~ Char) => IsString (Parsor s s m () ()) where
  fromString = terminal
instance (Subtextual s m, Item s ~ Char) => IsString (Parsor s s m s s) where
  fromString = tokens

instance Functor (Printor s t f a) where
  fmap _ = coerce
instance Contravariant (Printor s t f a) where
  contramap _ = coerce
instance Profunctor (Printor s t f) where
  dimap f _ = Printor . lmap f . runPrintor
  lmap f = Printor . lmap f . runPrintor
  rmap _ = coerce
instance Functor f => Tetradic f Printor where
  dimapT h i = Printor . (fmap (fmap (dimap h i))) . runPrintor
  tetramap h i f _ = Printor . dimap f (fmap (dimap h i)) . runPrintor

instance Filterable (Printor s t f a) where
  mapMaybe _ (Printor p) = Printor p
instance Cochoice (Printor s t f) where
  unleft = fst . filtrate
  unright = snd . filtrate
instance Filtrator (Printor s t f) where
  filtrate (Printor p) = (Printor (p . Left), Printor (p . Right))

instance Applicative f => Applicative (Printor s s f a) where
  pure _ = Printor (\_ -> pure id)
  Printor p <*> Printor q = Printor (\a -> (.) <$> p a <*> q a)
instance Alternative f => Alternative (Printor s s f a) where
  empty = Printor (\_ -> empty)
  Printor p <|> Printor q = Printor (\a -> p a <|> q a)
instance Alternative f => Choice (Printor s s f) where
  left' = alternate . Left
  right' = alternate . Right
instance Applicative f => Distributor (Printor s s f) where
  zeroP = Printor absurd
  Printor p >+< Printor q = Printor (either p q)
instance Alternative f => Alternator (Printor s s f) where
  alternate = \case
    Left (Printor p) -> Printor (either p (\_ -> empty))
    Right (Printor p) -> Printor (either (\_ -> empty) p)

instance (Subtextual s m, Item s ~ a) => Tokenized (Printor s s m a a) where
  type Token (Printor s s m a a) = a
  anyToken = Printor (pure . cons)
instance (Subtextual s m, Item s ~ a) => Equator a a (Printor s s m) where
  equate = anyToken
instance Subtextual s m => TerminalSymbol (Printor s s m () ()) where
  type Alphabet (Printor s s m () ()) = Item s
instance (Subtextual s m, Item s ~ Char)
  => IsString (Printor s s m () ()) where
  fromString = terminal
instance (Subtextual s m, Item s ~ Char)
  => IsString (Printor s s m s s) where
  fromString = tokens

instance Functor f => Functor (Lintor s t f a) where
  fmap f = Lintor . fmap (fmap (first' f)) . runLintor
instance Functor f => Profunctor (Lintor s t f) where
  dimap f g = Lintor . dimap f (fmap (first' g)) . runLintor
instance Functor f => Tetradic f Lintor where
  dimapT f g = Lintor . rmap (fmap (second' (dimap f g))) . runLintor
  tetramap f g h i = Lintor . dimap h (fmap (i >*< dimap f g)) . runLintor
instance Applicative f => Applicative (Lintor s s f a) where
  pure b = Lintor (\_ -> pure (b, id))
  Lintor f <*> Lintor x = Lintor $ \c ->
    liftA2 (\(g, p) (a, q) -> (g a, p . q)) (f c) (x c)
instance Alternative f => Alternative (Lintor s s f a) where
  empty = Lintor (\_ -> empty)
  Lintor p <|> Lintor q = Lintor (\a -> p a <|> q a)
instance Filterable f => Filterable (Lintor s s f a) where
  mapMaybe f (Lintor p) = Lintor $
    mapMaybe (\(a,q) -> fmap (, q) (f a)) . p
instance Monad f => Monad (Lintor s s f a) where
  return = pure
  mx >>= f = Lintor $ \ctx -> do
    (x, p) <- runLintor mx ctx
    (y, q) <- runLintor (f x) ctx
    return (y, p . q)
instance (Alternative f, Monad f) => MonadPlus (Lintor s s f a)
instance Monadic (Lintor s s) where
  joinP (Lintor mf) = Lintor $ \a -> do
    (mb, f) <- mf a
    b <- mb
    return (b, f)
instance Polyadic Lintor where
  composeP (Lintor mf) = Lintor $ \a -> do
    (Lintor mg, f) <- mf a
    (b, g) <- mg a
    return (b, g . f)
instance Applicative f => Distributor (Lintor s s f) where
  zeroP = Lintor absurd
  Lintor p >+< Lintor q = Lintor $
    either (fmap (first' Left) . p) (fmap (first' Right) . q)
instance Alternative f => Alternator (Lintor s s f) where
  alternate = \case
    Left (Lintor p) -> Lintor $
      either (fmap (first' Left) . p) (\_ -> empty)
    Right (Lintor p) -> Lintor $
      either (\_ -> empty) (fmap (first' Right) . p)
instance Filterable f => Filtrator (Lintor s s f) where
  filtrate (Lintor p) =
    ( Lintor (mapMaybe (\case{(Left b, q) -> Just (b, q); _ -> Nothing}) . p . Left)
    , Lintor (mapMaybe (\case{(Right b, q) -> Just (b, q); _ -> Nothing}) . p . Right)
    )
instance Alternative f => Choice (Lintor s s f) where
  left' = alternate . Left
  right' = alternate . Right
instance Filterable f => Cochoice (Lintor s s f) where
  unleft = fst . filtrate
  unright = snd . filtrate
instance Functor f => Strong (Lintor s s f) where
  first' (Lintor p) = Lintor (\(a,c) -> fmap (\(b,q) -> ((b,c),q)) (p a))
  second' (Lintor p) = Lintor (\(c,a) -> fmap (\(b,q) -> ((c,b),q)) (p a))
instance Monad f => Category (Lintor s s f) where
  id = Lintor $ \a -> return (a, id)
  Lintor q . Lintor p = Lintor $ \a -> do
    (b, p') <- p a
    (c, q') <- q b
    return (c, q' . p')
instance Monad f => Arrow (Lintor s s f) where
  arr f = Lintor (return . (, id) . f)
  (***) = (>*<)
  first = first'
  second = second'

instance (Subtextual s m, Item s ~ a) => Tokenized (Lintor s s m a a) where
  type Token (Lintor s s m a a) = a
  anyToken = Lintor (\b -> pure (b, cons b))
instance (Subtextual s m, Item s ~ a) => Equator a a (Lintor s s m) where
  equate = anyToken
instance Subtextual s m => TerminalSymbol (Lintor s s m () ()) where
  type Alphabet (Lintor s s m () ()) = Item s
instance (Subtextual s m, Item s ~ Char) => IsString (Lintor s s m () ()) where
  fromString = terminal
instance (Subtextual s m, Item s ~ Char) => IsString (Lintor s s m s s) where
  fromString = tokens

instance Functor (SyntaxP s t f a) where fmap _ = coerce
instance Contravariant (SyntaxP s t f a) where contramap _ = coerce
instance Profunctor (SyntaxP s t f) where dimap _ _ = coerce
instance Bifunctor (SyntaxP s t f) where bimap _ _ = coerce
instance Functor f => Tetradic f SyntaxP where
  dimapT _ g = SyntaxP . fmap g . runSyntaxP
  tetramap _ g _ _ = SyntaxP . fmap g . runSyntaxP
instance Choice (SyntaxP s t f) where
  left' = coerce
  right' = coerce
instance (Monoid t, Applicative f)
  => Applicative (SyntaxP s t f a) where
  pure _ = SyntaxP (pure mempty)
  SyntaxP rex1 <*> SyntaxP rex2 =
    SyntaxP (liftA2 (<>) rex1 rex2)
instance (KleeneStarAlgebra t, Applicative f) => Alternative (SyntaxP s t f a) where
  empty = SyntaxP (pure failK)
  SyntaxP rex1 <|> SyntaxP rex2 =
    SyntaxP (liftA2 altK rex1 rex2)
  many (SyntaxP rex) = SyntaxP (fmap starK rex)
  some (SyntaxP rex) = SyntaxP (fmap plusK rex)
instance (KleeneStarAlgebra t, Applicative f) => Distributor (SyntaxP s t f) where
  zeroP = SyntaxP (pure failK)
  SyntaxP rex1 >+< SyntaxP rex2 =
    SyntaxP (liftA2 altK rex1 rex2)
  manyP (SyntaxP rex) = SyntaxP (fmap starK rex)
  optionalP (SyntaxP rex) = SyntaxP (fmap optK rex)
instance (KleeneStarAlgebra t, Applicative f) => Alternator (SyntaxP s t f) where
  alternate = either coerce coerce
  someP (SyntaxP rex) = SyntaxP (fmap plusK rex)
instance (Tokenized t, Categorized c, Token t ~ c, Applicative f)
  => Tokenized (SyntaxP s t f c c) where
  type Token (SyntaxP s t f c c) = Token t
  anyToken = SyntaxP (pure anyToken)
  token = SyntaxP . pure . token
  inClass = SyntaxP . pure . inClass
  notInClass = SyntaxP . pure . notInClass
  inCategory = SyntaxP . pure . inCategory
  notInCategory = SyntaxP . pure . notInCategory
instance Applicative f => TerminalSymbol (SyntaxP s (RegEx c) f () ()) where
  type Alphabet (SyntaxP s (RegEx c) f () ()) = c
  terminal = SyntaxP . pure . terminal
