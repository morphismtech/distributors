{-# LANGUAGE ConstraintKinds, ImpredicativeTypes, ScopedTypeVariables #-}
module Text.Distributor.Grammar2
  ( Tokenized (token), satisfies, restOfStream, endOfStream
  , Syntactic (terminal)
  , Grammatical (ruleRec, rule)
  , TextualPartial, TextualTotal
  , Grammar (Grammar, grammarRules, grammarStart)
  , runGrammar
  , Prod (..)
  , production
  , Parser (Parser, runParser)
  , Printer (Printer, runPrinter)
  , Linter (Linter, runLinter)
  -- , Expr (..)
  -- , expr
  ) where

import Control.Applicative ( Alternative(..) )
import Control.Lens
    ( Choice(..),
      Profunctor(dimap, rmap),
      cons,
      view,
      makePrisms,
      only )
import Control.Lens.PartialIso ( (>?<), (>?), (?<), _Guard, mapMaybeP )
import Control.Lens.Stream
    ( SimpleStream, nil, _HeadTailMay, _ConvertStream )
import Control.Monad ( MonadPlus(mzero) )
import Data.Bifunctor.Joker ( Joker(Joker) )
-- import Data.Char ( isDigit )
import Data.Coerce ( coerce )
import Data.Function (fix)
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as Map
import Data.Distributor
import Data.Profunctor ( Cochoice(..), Forget(..) )
import Data.String ( IsString(..) )
import Text.ParserCombinators.ReadP ( ReadP, get )
import Witherable ( Filterable(catMaybes, mapMaybe) )

class Tokenized a b p | p -> a, p -> b where
  token :: p a b

data Token a b s t where
  Token :: Token a b a b
instance Tokenized a b (Token a b) where token = Token

satisfies
  :: ( Tokenized c c p
     , Choice p
     , Cochoice p
     )
  => (c -> Bool)
  -> p c c
satisfies f = _Guard f >?< token

restOfStream
  :: ( Tokenized a b p
     , SimpleStream s a
     , SimpleStream t b
     , Distributor p
     )
  => p s t
restOfStream = several token

endOfStream
  :: forall c p.
     ( Tokenized c c p
     , Eq c
     , Cochoice p
     , Distributor p
     )
  => p () ()
endOfStream = only @[c] [] ?< restOfStream

class
  ( Monoidal p
  , Cochoice p
  , forall x. Applicative (p x)
  ) => Syntactic t p | p -> t where
  terminal :: t -> p () ()
  default terminal
    :: ( Eq c
       , SimpleStream t c
       , Tokenized c c p
       )
    => t -> p () ()
  terminal str = case view _HeadTailMay str of
    Nothing -> oneP
    Just (c,t) -> (only c ?< token) >* terminal t

class
  ( Syntactic t p
  , Distributor p
  ) => Grammatical t p where
  rule :: String -> p a b -> p a b
  rule name p = ruleRec name (\_ -> p)
  ruleRec :: String -> (p a b -> p a b) -> p a b
  ruleRec _ = fix

type TextualTotal p =
  ( IsString (p () ())
  , Tokenized Char Char p
  , Grammatical String p
  )

type TextualPartial p =
  ( TextualTotal p
  , Choice p
  , forall x. Alternative (p x)
  )

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

production :: TextualPartial p => p (Prod Char) (Prod Char)
production = ruleRec "production" $ \prod ->
  prodToken
  <|> prodTerminal
  <|> prodEmpty
  <|> prodSeq prod
  <|> prodOr prod
  <|> prodSev prod
  <|> prodSev1 prod
  <|> prodPoss prod
  where
    prodToken = rule "token" $ _ProdToken >? terminal "[token]"
    prodTerminal = rule "terminal" $ _ProdTerminal >? quote >* several notQuote *< quote
    prodEmpty = rule "empty" $ _ProdEmpty >? empty
    prodSeq prod = rule "seq" $ _ProdSeq >? prod *< terminal " " >*< prod
    prodOr prod = rule "or" $ _ProdOr >? prod *< terminal " | " >*< prod
    prodSev prod = rule "*" $ _ProdSev >? parens prod *< terminal "*"
    prodSev1 prod = rule "+" $ _ProdSev1 >? parens prod *< terminal "+"
    prodPoss prod = rule "?" $ _ProdSev >? parens prod *< terminal "?"
    quote = terminal "\'"
    notQuote = satisfies (/= '\'')
    parens x = terminal "(" >* x *< terminal ")*"

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
  several (Grammar s rules) = Grammar (ProdSev s) rules
  severalMore (Grammar s rules) = Grammar (ProdSev1 s) rules
  possibly (Grammar s rules) = Grammar (ProdPoss s) rules
instance Choice (Grammar c) where
  left' = coerce
  right' = coerce
instance Cochoice (Grammar c) where
  unleft = coerce
  unright = coerce
instance () => Tokenized c c (Grammar c) where
  token = Grammar ProdToken Map.empty
instance Eq c => Syntactic [c] (Grammar c) where
  terminal t = Grammar (ProdTerminal (view _ConvertStream t)) Map.empty
instance Eq c => Grammatical [c] (Grammar c) where
  ruleRec name f =
    let Grammar s rules = f (Grammar (ProdNonTerminal name) Map.empty)
    in Grammar (ProdNonTerminal name) (rules <> Map.singleton name s)
instance (x ~ (), y ~ ()) => IsString (Grammar Char x y) where
  fromString = terminal

runGrammar :: String -> Grammar Char x y -> [(String,Maybe String)]
runGrammar start (Grammar s rules)
  = (start, runLinter production s)
  : [(name, runLinter production r) | (name, r) <- Map.toList rules]

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
instance Tokenized Char Char (Parser ReadP) where
  token = Parser get
instance Syntactic String (Parser ReadP)
instance Grammatical String (Parser ReadP)
instance (x ~ (), y ~ ()) => IsString (Parser ReadP x y) where
  fromString = terminal

newtype Printer t a b = Printer {runPrinter :: a -> t}
  deriving
    ( Profunctor
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
instance Filterable (Printer t a) where
  mapMaybe _ (Printer x) = Printer x
instance SimpleStream t c => Tokenized c c (Printer t) where
  token = Printer (`cons` nil)
instance (Eq c, SimpleStream t c) => Syntactic t (Printer t)
instance (Eq c, SimpleStream t c) => Grammatical t (Printer t)
instance (x ~ (), y ~ (), SimpleStream t Char)
  => IsString (Printer t x y) where
    fromString = terminal . view _ConvertStream

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
instance (Applicative f, SimpleStream t c)
  => Tokenized c c (Linter f t) where
    token = Linter (pure . (`cons` nil))
instance (Eq c, Applicative f, SimpleStream t c) => Syntactic t (Linter f t)
instance (Alternative f, Filterable f, Eq c, SimpleStream t c)
  => Grammatical t (Linter f t) where
instance (x ~ (), y ~ (), Alternative f, SimpleStream s Char)
  => IsString (Linter f s x y) where
    fromString = terminal . view _ConvertStream

data Expr = Plus Expr Expr | Mult Expr Expr | Numb Integer
    deriving Show
makePrisms ''Expr

-- expr :: Grammatical Char p => p Expr Expr
-- expr = recNonTerminal "expr" $ \ x -> ePlus x

-- ePlus :: Grammatical Char p => p Expr Expr -> p Expr Expr
-- ePlus x = rule "plus" $
--   dichainl _Plus (terminal ("+" :: String)) (eMult x)

-- eMult :: Grammatical Char p => p Expr Expr -> p Expr Expr
-- eMult x = rule "plus" $
--   dichainl _Mult (terminal ("*" :: String)) (eAtom x)

-- eAtom :: Grammatical Char p => p Expr Expr -> p Expr Expr
-- eAtom x = rule "atom" $ eNumb <|> eParens x
  
-- eNumb :: Grammatical Char p => p Expr Expr
-- eNumb = _Numb >?
--   dimap show read (several1 (satisfies isDigit))

-- eParens :: Grammatical Char p => p Expr Expr -> p Expr Expr
-- eParens x = terminal ("(" :: String) >* x *< terminal (")" :: String)
