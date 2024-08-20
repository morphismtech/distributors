{-# LANGUAGE ConstraintKinds, ImpredicativeTypes, ScopedTypeVariables #-}
module Text.Distributor.Grammar
  ( Grammatical (..)
  , PartialGrammatical (..)
  , Textual (..)
  , PartialTextual (..)
  , Syntactic (..)
  , satisfy
  , allTokens
  , end
  , Parser (Parser, runParser)
  , Printer (Printer, runPrinter)
  , Linter (Linter, runLinter)
  , Prod (..)
  , Grammar (Grammar, grammarRules, grammarStart)
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.Bifocal
import Control.Lens.PartialIso
import Control.Lens.Stream
import Control.Monad
import Data.Bifunctor.Joker
import Data.Coerce
import Data.Function
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as Map
import Data.Profunctor
import Data.Profunctor.Choose
import Data.Profunctor.Distributor
import Data.Profunctor.Monoidal
import Data.String
import GHC.IsList
import Text.ParserCombinators.ReadP ( ReadP, get )
import Witherable

class Grammatical rul str chr x where
  gramma ::
    ( Syntactic rul str chr p
    , Applicative f
    ) => Optic p f x x a b

class PartialGrammatical e t c a where
  grampa ::
    ( Syntactic e t c p
    , Choice p
    , forall x. Alternative (p x)
    , IsList (p () ())
    , Item (p () ()) ~ c
    ) => p a a

class Textual e t a where
  textGramma ::
    ( Syntactic e t Char p
    , IsString (p () ())
    ) => p a a

class PartialTextual e t a where
  textGrampa ::
    ( Syntactic e t Char p
    , Choice p
    , forall x. Alternative (p x)
    , IsString (p () ())
    ) => p a a

class
  ( Eq c
  , SimpleStream t c
  , Distributor p
  , Cochoice p
  , forall x. Filterable (p x)
  , forall x. Applicative (p x)
  ) => Syntactic e t c p
  | p -> e, p -> c, p -> t where
    anyToken :: p c c
    stream :: t -> p a ()
    stream str = case view _HeadTailMay str of
      Nothing -> pureP ()
      Just (c,t) -> (only c ?< anyToken) >* stream t
    rule :: e -> p a b -> p a b
    rule e p = ruleRec e (\_ -> p)
    ruleRec :: e -> (p a b -> p a b) -> p a b
    ruleRec _ = fix

type Syntax rul str chr s t a b = forall p f.
  (Syntactic rul str chr p, f ~ Identity)
    => p a (f b) -> p s (f t)

type Syntax' rul str chr s a = Syntax rul str chr s s a a

_Any :: Syntax' rul str chr chr ()
_Any = (rmap pure anyToken *<)

_TilEnd :: Syntax' rul str chr str ()
_TilEnd = _Many . _Any

_Str :: str -> Syntax' rul str chr () ()
_Str t = (rmap pure (stream t) *<)

_Chr :: chr -> Syntax' rul str chr () ()
_Chr c =  _Str (cons c nil)

_End :: forall str chr rul p. (Syntactic rul str chr p) => Optic' p Identity () ()
_End = _Match (_Nil @str @chr) . _TilEnd

_Match :: (Cochoice p, Identity ~ f) => APrism b a t s -> Optic p f s t a b
_Match coprism =
  rmap Identity . (coprism ?<) . rmap runIdentity

allTokens :: (Syntactic e t c p, Stream s t c c) => p s t
allTokens = manyP anyToken

end
  :: forall t c p e.
     Syntactic e t c p
  => p () ()
end = _Nil @t ?< allTokens

satisfy
  :: ( Choice p
     , Syntactic e t c p
     )
  => (c -> Bool)
  -> p c c
satisfy f = _Satisfy f >?< anyToken

newtype Parser f a b = Parser {runParser :: f b}
  deriving
    ( Profunctor
    , Choice
    , Monoidal
    , Distributor
    ) via Joker f
  deriving Functor via Joker f a
instance Applicative f => Applicative (Parser f a) where
  pure = pureP
  (<*>) = apP
instance Alternative f => Alternative (Parser f a) where
  empty = Parser empty
  Parser x <|> Parser y = Parser (x <|> y)
instance MonadPlus f => Filterable (Parser f a) where
  mapMaybe f (Parser x) =
    Parser (maybe mzero return . f =<< x)
instance MonadPlus f => Cochoice (Parser f) where
  unleft (Parser f) =
    Parser (either return (const mzero) =<< f)
  unright (Parser f) =
    Parser (either (const mzero) return =<< f)
instance Syntactic String String Char (Parser ReadP) where
  anyToken = Parser get
instance (x ~ (), y ~ ()) => IsString (Parser ReadP x y) where
  fromString = stream

newtype Printer t a b = Printer {runPrinter :: a -> t}
  deriving
    ( Profunctor
    , Choice
    , Cochoice
    , Monoidal
    , Distributor
    ) via Forget t
  deriving
    ( Functor
    ) via Forget t a
instance Monoid t => Applicative (Printer t a) where
  pure = pureP
  (<*>) = apP
instance (Monoid t, Nil t b) => Alternative (Printer t a) where
  empty = catMaybes (pure Nothing)
  Printer x <|> Printer y = Printer $ \a ->
     case matching _Nil (x a) of
      Left t -> t
      Right _ -> y a
instance Filterable (Printer t a) where
  mapMaybe _ (Printer x) = Printer x
instance (Eq c, SimpleStream t c, IsList t, Item t ~ c)
  => Syntactic String t c (Printer t) where
    anyToken = Printer (`cons` nil)
instance (x ~ (), y ~ (), SimpleStream t Char, IsList t, Item t ~ Char)
  => IsString (Printer t x y) where
    fromString = stream . view _Tokens

newtype Linter f t a b = Linter {runLinter :: a -> f t}
instance Functor (Linter f t a) where
  fmap _ (Linter f) = Linter f
instance Profunctor (Linter f t) where
  dimap g _ (Linter linter) = Linter (linter . g)
instance (Applicative f, Monoid t) => Applicative (Linter f t a) where
  pure _ = Linter (\_ -> pure mempty)
  Linter l <*> Linter r = Linter $ \a -> liftA2 (<>) (l a) (r a)
instance (Alternative f, Monoid t) => Alternative (Linter f t a) where
  empty = Linter (\_ -> empty)
  Linter l <|> Linter r = Linter $ \a -> l a <|> r a
instance (Applicative f, Filterable f) => Filterable (Linter f t a) where
  mapMaybe = mapMaybeP
instance (Applicative f, Monoid t) => Monoidal (Linter f t)
instance Cochoice (Linter f t) where
  unleft (Linter linter) = Linter $ linter . Left
  unright (Linter linter) = Linter $ linter . Right
instance (Applicative f, Filterable f) => Choice (Linter f t) where
  left' (Linter linter) = Linter $
    either linter (\_ -> catMaybes (pure Nothing))
  right' (Linter linter) = Linter $
    either (\_ -> catMaybes (pure Nothing)) linter
instance (Alternative f, Filterable f, Monoid t) => Distributor (Linter f t)
instance (Eq c, Alternative f, Filterable f, SimpleStream t c)
  => Syntactic String t c (Linter f t) where
    anyToken = Linter (pure . (`cons` nil))
instance (x ~ (), y ~ (), Alternative f, Filterable f, SimpleStream s Char)
  => IsString (Linter f s x y) where
    fromString = stream . view _Tokens

data Grammar c a b = Grammar
  { grammarStart :: Prod c
  , grammarRules :: Map String (Prod c)
  } deriving (Eq, Ord, Read, Show)
instance Functor (Grammar c a) where
  fmap = rmap
instance Eq c => Applicative (Grammar c a) where
  pure = pureP
  (<*>) = apP
instance Filterable (Grammar c a) where
  mapMaybe = mapMaybeP
instance Eq c => Alternative (Grammar c a) where
  empty = Grammar ProdEmpty Map.empty
  Grammar ProdEmpty rules0 <|> Grammar s1 rules1 =
    Grammar s1 (rules0 <> rules1)
  Grammar s0 rules0 <|> Grammar ProdEmpty rules1 =
    Grammar s0 (rules0 <> rules1)
  Grammar s0 rules0 <|> Grammar s1 rules1 =
    Grammar (ProdOr s0 s1) (rules0 <> rules1)
  many (Grammar s rules) = Grammar (ProdSev s) rules
  some (Grammar s rules) = Grammar (ProdSev1 s) rules
instance Profunctor (Grammar c) where
  dimap _ _ = coerce
instance Monoidal (Grammar c) where
  oneP = Grammar (ProdTerminal []) Map.empty
  Grammar (ProdTerminal []) rules0 >*< Grammar s1 rules1 =
    Grammar s1 (rules0 <> rules1)
  Grammar s0 rules0 >*< Grammar (ProdTerminal []) rules1 =
    Grammar s0 (rules0 <> rules1)
  Grammar s0 rules0 >*< Grammar s1 rules1 =
    Grammar (ProdSeq s0 s1) (rules0 <> rules1)
instance Distributor (Grammar c) where
  zeroP = Grammar ProdEmpty Map.empty
  Grammar ProdEmpty rules0 >+< Grammar s1 rules1 =
    Grammar s1 (rules0 <> rules1)
  Grammar s0 rules0 >+< Grammar ProdEmpty rules1 =
    Grammar s0 (rules0 <> rules1)
  Grammar s0 rules0 >+< Grammar s1 rules1 =
    Grammar (ProdOr s0 s1) (rules0 <> rules1)
  manyP (Grammar s rules) = Grammar (ProdSev s) rules
  many1 (Grammar s rules) = Grammar (ProdSev1 s) rules
  optionP (Grammar s rules) = Grammar (ProdPoss s) rules
instance Choice (Grammar c) where
  left' = coerce
  right' = coerce
instance Cochoice (Grammar c) where
  unleft = coerce
  unright = coerce
instance Eq c => Syntactic String [c] c (Grammar c) where
  anyToken = Grammar ProdToken Map.empty
  stream t = Grammar (ProdTerminal (view _Tokens t)) Map.empty
  ruleRec name f =
    let Grammar s rules = f (Grammar (ProdNonTerminal name) Map.empty)
    in Grammar (ProdNonTerminal name) (rules <> Map.singleton name s)
instance (x ~ (), y ~ ()) => IsString (Grammar Char x y) where
  fromString = stream

data Prod c
  = ProdToken
  | ProdTerminal [c]
  | ProdNonTerminal String
  | ProdEmpty
  | ProdSeq (Prod c) (Prod c)
  | ProdOr (Prod c) (Prod c)
  | ProdSev (Prod c)
  | ProdSev1 (Prod c)
  | ProdPoss (Prod c)
  deriving (Eq, Ord, Read, Show)
makePrisms ''Prod
