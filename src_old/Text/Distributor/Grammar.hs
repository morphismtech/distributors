{-# LANGUAGE ConstraintKinds, ImpredicativeTypes, ScopedTypeVariables #-}
module Text.Distributor.Grammar
  ( Grammatical (..)
  , Syntactic (..)
  , satisfy
  , allTokens
  , end
  , Parser (Parser, runParser)
  , Printer (Printer, runPrinter)
  , Linter (Linter, runLinter)
  , Prod (..)
  , Grammar (Grammar, grammarRules, grammarStart)
  , ShowReadP (..)
  , readP
  , showP
  , showRead
  ) where

import Control.Applicative
import Control.Lens
-- import Control.Lens.Bifocal
import Control.Lens.PartialIso
import Control.Lens.Stream
import Data.Bifunctor.Joker
import Data.Void
import Data.Coerce
import Data.Function
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as Map
import Data.Profunctor
import Data.Profunctor.Partial
import Data.Profunctor.Distributor
import Data.Profunctor.Monoidal
import Data.String
import GHC.IsList
import qualified Text.ParserCombinators.ReadP as ReadP
import Text.ParserCombinators.ReadP (ReadP)
import Witherable

class Grammatical rul str chr s a where
  grammar :: Syntax rul str chr s a

class
  ( Eq chr
  , Stream' str chr
  , Distributor p
  , Choice p
  , Cochoice p
  , forall x. Filterable (p x)
  , forall x. Alternative (p x)
  ) => Syntactic rul str chr p
  | p -> rul, p -> chr, p -> str where
    anyToken :: p chr chr
    stream :: str -> p a ()
    stream str = case view _HeadTailMay str of
      Nothing -> pureP ()
      Just (c,t) -> (only c ?< anyToken) >* stream t
    rule :: rul -> p a b -> p a b
    rule e p = ruleRec e (\_ -> p)
    ruleRec :: rul -> (p a b -> p a b) -> p a b
    ruleRec _ = fix

type Syntactical rul str chr s t a b = forall p.
  Syntactic rul str chr p
    => p a (Identity b) -> p s (Identity t)

type Syntax rul str chr s a = Syntactical rul str chr s s a a

_Any :: Syntax rul str chr chr ()
_Any = (rmap pure anyToken *<)

-- _TilEnd :: Syntax rul str chr str ()
-- _TilEnd = _Many . _Any

_Str :: str -> Syntax rul str chr () ()
_Str t = (rmap pure (stream t) *<)

_Chr :: chr -> Syntax rul str chr () ()
_Chr c =  _Str (cons c Empty)

-- _End :: forall rul str chr. Syntax rul str chr () ()
-- _End = coPrism (_Empty @str) . _TilEnd

allTokens :: (Syntactic e t c p, Stream s t c c) => p s t
allTokens = manyP anyToken

end
  :: forall t c p e.
     Syntactic e t c p
  => p () ()
end = _Empty @t ?< allTokens

satisfy
  :: ( Syntactic e t c p
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
instance Filterable f => Cochoice (Parser f) where
  unleft (Parser f) =
    Parser (mapMaybe (either Just (const Nothing)) f)
  unright (Parser f) =
    Parser (mapMaybe (either (const Nothing) Just) f)
instance Filterable f => Filterable (Parser f a) where
  mapMaybe f (Parser x) = Parser (mapMaybe f x)
instance Filterable ReadP where
  catMaybes m = m >>= maybe ReadP.pfail return
instance Syntactic Void String Char (Parser ReadP) where
  anyToken = Parser ReadP.get

showP :: ShowReadP a b -> a -> String
showP (ShowReadP s _) a = s a ""
readP :: ShowReadP a b -> String -> [(b, String)]
readP (ShowReadP _ r) str = ReadP.readP_to_S r str
showRead :: (Show a, Read a) => ShowReadP a a
showRead = ShowReadP shows (ReadP.readS_to_P reads)
data ShowReadP a b = ShowReadP (a -> ShowS) (ReadP b)
instance Profunctor ShowReadP where
  dimap f g (ShowReadP s r) = ShowReadP (s . f) (g <$> r)
instance Functor (ShowReadP a) where fmap = rmap
instance Applicative (ShowReadP a) where
  pure b = ShowReadP (\_ -> id) (pure b)
  ShowReadP sx rx <*> ShowReadP sy ry =
    ShowReadP (\a -> sx a . sy a) (rx <*> ry)
instance Monoidal ShowReadP
instance Choice ShowReadP where
  left' (ShowReadP s r) = ShowReadP
    (either s (const id))
    (runParser (left' (Parser r)))
  right' (ShowReadP s r) = ShowReadP
    (either (const id) s)
    (runParser (right' (Parser r)))
instance Cochoice ShowReadP where
  unleft (ShowReadP s r) = ShowReadP
    (s . Left)
    (r >>= either return (\_ -> ReadP.pfail))
instance Filterable (ShowReadP a) where
  catMaybes (ShowReadP s r) =
    ShowReadP s (r >>= maybe ReadP.pfail return)
instance Alternative (ShowReadP a) where
  empty = ShowReadP (\_ -> id) ReadP.pfail
  ShowReadP xs xr <|> ShowReadP ys yr = ShowReadP
    (\a -> if isn't _Empty (xs a "") then xs a else ys a)
    (xr ReadP.+++ yr)
  many shrd = lmap (:[]) (manyP shrd)
instance Distributor ShowReadP where
  manyP (ShowReadP sh rd) = ShowReadP
    (\s -> foldl (.) id [sh a | a <- view _Tokens s])
    (view _Tokens <$> many rd)
instance Syntactic Void String Char ShowReadP where
  anyToken = ShowReadP (:) ReadP.get
instance (a ~ (), b ~ ()) => IsString (ShowReadP a b) where
  fromString = stream

newtype Printer t a b = Printer {runPrinter :: a -> t}
  deriving
    ( Profunctor
    , Choice
    , Cochoice
    , Strong
    , Monoidal
    , Distributor
    ) via Forget t
  deriving
    ( Functor
    ) via Forget t a
instance Monoid t => Applicative (Printer t a) where
  pure = pureP
  (<*>) = apP
instance (Monoid t, AsEmpty t) => Alternative (Printer t a) where
  empty = catMaybes (pure Nothing)
  Printer x <|> Printer y = Printer $ \a ->
     case matching _Empty (x a) of
      Left t -> t
      Right _ -> y a
instance Filterable (Printer t a) where
  mapMaybe _ (Printer x) = Printer x
instance (Eq c, Stream' t c, IsList t, Item t ~ c)
  => Syntactic String t c (Printer t) where
    anyToken = Printer (`cons` Empty)
instance (x ~ (), y ~ (), Stream' t Char, IsList t, Item t ~ Char)
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
instance (Eq c, Alternative f, Filterable f, Stream' t c)
  => Syntactic String t c (Linter f t) where
    anyToken = Linter (pure . (`cons` Empty))
instance (x ~ (), y ~ (), Alternative f, Filterable f, Stream' s Char)
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
  optionalP (Grammar s rules) = Grammar (ProdPoss s) rules
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

{-
module Text.Distributor.Grammar2
  ( Syntactic (..)
  , Grammatical (..)
  ) where

class
  ( PartialDistributor p
  , Tokenized a b p
  , Stream s t a b
  , Cons s t a b
  , Eq a
  , Eq b
  ) => Syntactic s t a b p where
    stream :: s -> p x ()
    stream str = case view _HeadTailMay str of
      Nothing -> pureP ()
      Just (h,t) -> (only h ?< anyToken) >* stream t

class Syntactic s t a b p => Grammatical s t a b p where
  rule :: String -> p x y -> p x y
  rule _ = id
  ruleRec :: String -> (p x y -> p x y) -> p x y
  ruleRec e f = rule e (fix f)
-}
