{-# LANGUAGE ConstraintKinds #-}
module Text.Distributor.Grammar
  ( Grammatical (token, terminal, recNonTerminal, nonTerminal)
  , fromList, satisfies, restOfStream, endOfStream
  , Grammar (Grammar, grammarRules, grammarStart)
  , Production (..), production
  , Parser (Parser, runParser)
  -- , Printer (Printer, runPrinter)
  , Linter (Linter, runLinter)
  , Expr (..)
  , expr
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
import Data.Char ( isDigit )
import Data.Coerce ( coerce )
import Data.Function (fix)
import Data.List (nub)
import Data.Distributor
    ( Distributor(..),
      Monoidal(..),
      pureP,
      apP,
      (>*),
      (*<),
      several1,
      dichainl )
import Data.Profunctor ( Cochoice(..) )
import Data.String ( IsString(..) )
import Text.ParserCombinators.ReadP ( ReadP, get )
import Witherable ( Filterable(catMaybes, mapMaybe) )

class
  ( Eq c
  , Distributor p
  , Cochoice p
  , Choice p
  , forall a. Alternative (p a)
  ) => Grammatical c p | p -> c where
    token :: p c c
    terminal :: SimpleStream t c => t -> p () ()
    terminal str = case view _HeadTailMay str of
      Nothing -> oneP
      Just (c,t) -> (only c ?< token) >* terminal t
    recNonTerminal :: String -> (p a b -> p a b) -> p a b
    recNonTerminal _ = fix
    nonTerminal :: String -> p a b -> p a b
    nonTerminal s p = recNonTerminal s (\_ -> p)

fromList :: Grammatical c p => [c] -> p () ()
fromList = terminal

satisfies :: Grammatical c p => (c -> Bool) -> p c c
satisfies f = _Guard f >?< token

restOfStream :: (Grammatical c p, SimpleStream t c) => p t t
restOfStream = several token

endOfStream :: Grammatical c p => p () ()
endOfStream = only [] ?< restOfStream

data Production c
  = ProdToken
  | ProdTerminal [c]
  | ProdNonTerminal String
  | ProdEmpty
  | ProdSeq (Production c) (Production c)
  | ProdOr (Production c) (Production c)
  | ProdSev (Production c)
  | ProdSev1 (Production c)
  | ProdPoss (Production c)
  deriving (Eq, Ord, Read, Show)
makePrisms ''Production

production :: Grammatical Char p => p (Production Char) (Production Char)
production = recNonTerminal "production" $ \prod ->
  prodToken
  <|> prodTerminal
  <|> prodEmpty
  <|> prodSeq prod
  <|> prodOr prod
  <|> prodSev prod
  <|> prodSev1 prod
  <|> prodPoss prod
  where
    prodToken = nonTerminal "token" $ _ProdToken >? fromList "[token]"
    prodTerminal = nonTerminal "terminal" $ _ProdTerminal >? quote >* several notQuote *< quote
    prodEmpty = nonTerminal "empty" $ _ProdEmpty >? empty
    prodSeq prod = nonTerminal "seq" $ _ProdSeq >? prod *< fromList " " >*< prod
    prodOr prod = nonTerminal "or" $ _ProdOr >? prod *< fromList " | " >*< prod
    prodSev prod = nonTerminal "*" $ _ProdSev >? parens prod *< fromList "*"
    prodSev1 prod = nonTerminal "+" $ _ProdSev1 >? parens prod *< fromList "+"
    prodPoss prod = nonTerminal "?" $ _ProdSev >? parens prod *< fromList "?"
    quote = fromList "\'"
    notQuote = satisfies (/= '\'')
    parens x = fromList "(" >* x *< fromList ")*"

data Grammar c a b = Grammar
  { grammarRules :: [(String, Production c)]
  , grammarStart :: Production c
  } deriving (Eq, Ord, Read, Show)
type Prods c = [(String, Production c)]
mergeProds :: Eq c => Prods c -> Prods c -> Prods c
mergeProds x y = nub (x ++ y)
instance Functor (Grammar c a) where
  fmap = rmap
instance Eq c => Applicative (Grammar c a) where
  pure = pureP
  (<*>) = apP
instance Filterable (Grammar c a) where
  mapMaybe = mapMaybeP
instance Eq c => Alternative (Grammar c a) where
  empty = Grammar [] ProdEmpty

  Grammar rules0 ProdEmpty <|> Grammar rules1 s1 =
    Grammar (mergeProds rules0 rules1) s1
  Grammar rules0 s0 <|> Grammar rules1 ProdEmpty =
    Grammar (mergeProds rules0 rules1) s0
  Grammar rules0 s0 <|> Grammar rules1 s1 =
    Grammar (mergeProds rules0 rules1) (ProdOr s0 s1)

  many (Grammar rules s) = Grammar rules (ProdSev s)
  some (Grammar rules s) = Grammar rules (ProdSev1 s)
instance Profunctor (Grammar c) where
  dimap _ _ = coerce
instance Eq c => Monoidal (Grammar c) where
  oneP = Grammar [] (ProdTerminal [])

  Grammar rules0 (ProdTerminal []) >*< Grammar rules1 s1 =
    Grammar (mergeProds rules0 rules1) s1
  Grammar rules0 s0 >*< Grammar rules1 (ProdTerminal []) =
    Grammar (mergeProds rules0 rules1) s0
  Grammar rules0 s0 >*< Grammar rules1 s1 =
    Grammar (mergeProds rules0 rules1) (ProdSeq s0 s1)
instance Eq c => Distributor (Grammar c) where
  zeroP = Grammar [] ProdEmpty
  Grammar rules0 ProdEmpty >+< Grammar rules1 s1 =
    Grammar (mergeProds rules0 rules1) s1
  Grammar rules0 s0 >+< Grammar rules1 ProdEmpty =
    Grammar (mergeProds rules0 rules1) s0
  Grammar rules0 s0 >+< Grammar rules1 s1 =
    Grammar (mergeProds rules0 rules1) (ProdOr s0 s1)
  several (Grammar rules s) = Grammar rules (ProdSev s)
  severalMore (Grammar rules s) = Grammar rules (ProdSev1 s)
  possibly (Grammar rules s) = Grammar rules (ProdPoss s)
instance Choice (Grammar c) where
  left' = coerce
  right' = coerce
instance Cochoice (Grammar c) where
  unleft = coerce
  unright = coerce
instance Eq c => Grammatical c (Grammar c) where
  token = Grammar [] ProdToken
  terminal t = Grammar [] (ProdTerminal (view _ConvertStream t))
  recNonTerminal name rule =
    let Grammar rules s = rule (Grammar [] (ProdNonTerminal name))
    in Grammar (rules ++ [(name, s)]) (ProdNonTerminal name)
instance (x ~ (), y ~ ()) => IsString (Grammar Char x y) where
  fromString = terminal

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
instance Grammatical Char (Parser ReadP) where
  token = Parser get
instance (x ~ (), y ~ ()) => IsString (Parser ReadP x y) where
  fromString = terminal

-- newtype Printer t a b = Printer {runPrinter :: a -> t}
--   deriving
--     ( Profunctor
--     , Cochoice
--     , Monoidal
--     , Distributor
--     ) via Forget t
--   deriving
--     ( Functor
--     ) via Forget t a
-- instance Monoid t => Applicative (Printer t a) where
--   pure = pureP
--   (<*>) = apP
-- instance Filterable (Printer t a) where
--   mapMaybe _ (Printer x) = Printer x
-- instance (Eq c, SimpleStream t c) => Grammatical c (Printer t) where
--   token = Printer (`cons` nil)
-- instance (x ~ (), y ~ (), SimpleStream t Char)
--   => IsString (Printer t x y) where
--     fromString = terminal

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
instance (Alternative f, Filterable f, Eq c, SimpleStream t c)
  => Grammatical c (Linter f t) where
    token = Linter (pure . (`cons` nil))
instance (x ~ (), y ~ (), Alternative f, Filterable f, SimpleStream s Char)
  => IsString (Linter f s x y) where
    fromString = terminal

data Expr = Plus Expr Expr | Mult Expr Expr | Numb Integer
    deriving Show
makePrisms ''Expr

expr :: Grammatical Char p => p Expr Expr
expr = recNonTerminal "expr" $ \ x -> ePlus x

ePlus :: Grammatical Char p => p Expr Expr -> p Expr Expr
ePlus x = nonTerminal "plus" $
  dichainl _Plus (terminal ("+" :: String)) (eMult x)

eMult :: Grammatical Char p => p Expr Expr -> p Expr Expr
eMult x = nonTerminal "plus" $
  dichainl _Mult (terminal ("*" :: String)) (eAtom x)

eAtom :: Grammatical Char p => p Expr Expr -> p Expr Expr
eAtom x = nonTerminal "atom" $ eNumb <|> eParens x
  
eNumb :: Grammatical Char p => p Expr Expr
eNumb = _Numb >?
  dimap show read (several1 (satisfies isDigit))

eParens :: Grammatical Char p => p Expr Expr -> p Expr Expr
eParens x = terminal ("(" :: String) >* x *< terminal (")" :: String)
