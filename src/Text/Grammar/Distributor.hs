module Text.Grammar.Distributor
  ( Regular (..)
  , Grammatical (..)
  , ReadSyntax (..), runReadSyntax, readSyntax
  , ShowSyntax (ShowSyntax), runShowSyntax, showSyntax
  , Production (..), production
  , Grammar (..), grammar
  ) where

import Control.Applicative
import Control.Lens
-- import Control.Lens.Bifocal
import Control.Lens.PartialIso
import Control.Lens.Token
import Data.Char
import Data.Coerce
import Data.Function
import Data.Profunctor
import Data.Profunctor.Distributor
import Data.String
import Text.ParserCombinators.ReadP hiding (many, satisfy, char, sepBy)
import Witherable

class
  ( Alternator p
  , Filtrator p
  , Tokenized Char Char p
  , forall u. (u ~ () => IsString (p () u))
  ) => Regular p where
    char :: Char -> p () ()
    char c = mapCoprism (only c) anyToken
    charCategory :: GeneralCategory -> p Char Char
    charCategory cat = satisfy $ \ch -> cat == generalCategory ch

fromChars :: Regular p => String -> p () ()
fromChars [] = oneP
fromChars (c:cs) = char c *> fromChars cs

class Regular p => Grammatical p where
  rule :: String -> p a b -> p a b
  rule name p = ruleRec name (const p)
  ruleRec :: String -> (p a b -> p a b) -> p a b
  ruleRec _ = fix

newtype ShowSyntax a b = ShowSyntax (a -> Maybe ShowS)
instance Profunctor ShowSyntax where
  dimap f _ (ShowSyntax sh) = ShowSyntax (sh . f)
instance Functor (ShowSyntax a) where fmap = rmap
instance Applicative (ShowSyntax a) where
  pure _ = ShowSyntax (const (Just id))
  ShowSyntax sh0 <*> ShowSyntax sh1 =
    ShowSyntax (liftA2 (liftA2 (.)) sh0 sh1)
instance Alternative (ShowSyntax a) where
  empty = ShowSyntax (const Nothing)
  ShowSyntax sh0 <|> ShowSyntax sh1 =
    ShowSyntax (liftA2 (<|>) sh0 sh1)
  many (ShowSyntax sh) = ShowSyntax sh
  some (ShowSyntax sh) = ShowSyntax sh
instance Choice ShowSyntax where
  left' (ShowSyntax sh) =
    ShowSyntax (either sh (const Nothing))
  right' (ShowSyntax sh) =
    ShowSyntax (either (const Nothing) sh)
instance Cochoice ShowSyntax where
  unleft (ShowSyntax sh) = ShowSyntax (sh . Left)
  unright (ShowSyntax sh) = ShowSyntax (sh . Right)
instance Distributor ShowSyntax where
  manyP (ShowSyntax sh) = ShowSyntax shmany where
    shmany str =
      foldl (liftA2 (.)) (pure id) (map sh str)
instance Alternator ShowSyntax where
  someP (ShowSyntax sh) = ShowSyntax shsome where
    shsome str = do
      _ <- uncons str
      foldl (liftA2 (.)) (pure id) (map sh str)
instance Filtrator ShowSyntax
instance Filterable (ShowSyntax a) where
  mapMaybe = dimapMaybe Just
instance Tokenized Char Char ShowSyntax where
  anyToken = ShowSyntax (Just . (:))
instance u ~ () => IsString (ShowSyntax () u) where
  fromString = fromChars
instance Regular ShowSyntax
instance Grammatical ShowSyntax

newtype ReadSyntax a b = ReadSyntax (ReadP b)
instance Profunctor ReadSyntax where
  dimap _ g (ReadSyntax rd) = ReadSyntax (g <$> rd)
instance Functor (ReadSyntax a) where fmap = rmap
instance Applicative (ReadSyntax a) where
  pure b = ReadSyntax (pure b)
  ReadSyntax rd0 <*> ReadSyntax rd1 =
    ReadSyntax (rd0 <*> rd1)
instance Alternative (ReadSyntax a) where
  empty = ReadSyntax empty
  ReadSyntax rd0 <|> ReadSyntax rd1 =
    ReadSyntax (rd0 <|> rd1)
  many (ReadSyntax rd) = ReadSyntax (many rd)
  some (ReadSyntax rd) = ReadSyntax (some rd)
instance Choice ReadSyntax where
  left' (ReadSyntax rd) =
    ReadSyntax (Left <$> rd)
  right' (ReadSyntax rd) =
    ReadSyntax (Right <$> rd)
instance Cochoice ReadSyntax where
  unleft (ReadSyntax rd) =
    ReadSyntax (rd >>= either pure (const empty))
  unright (ReadSyntax rd) =
    ReadSyntax (rd >>= either (const empty) pure)
instance Distributor ReadSyntax where
  manyP (ReadSyntax rd) = ReadSyntax (many rd)
instance Alternator ReadSyntax where
  someP (ReadSyntax rd) = ReadSyntax (some rd)
instance Filtrator ReadSyntax
instance Filterable (ReadSyntax a) where
  mapMaybe = dimapMaybe Just
instance Tokenized Char Char ReadSyntax where
  anyToken = ReadSyntax get
instance Regular ReadSyntax
instance Grammatical ReadSyntax
instance u ~ () => IsString (ReadSyntax () u) where
  fromString = fromChars

runReadSyntax :: ReadSyntax a b -> String -> [(b, String)]
runReadSyntax (ReadSyntax rd) str = readP_to_S rd str

runShowSyntax :: ShowSyntax a b -> a -> Maybe String
runShowSyntax (ShowSyntax sh) a = ($ "") <$> sh a

showSyntax :: Show a => ShowSyntax a a
showSyntax = ShowSyntax (Just . shows)

readSyntax :: Read a => ReadSyntax a a
readSyntax = ReadSyntax (readS_to_P reads)

data Production c
  = AnyToken
  | Zero
  | Terminal [c]
  | NonTerminal String
  | Plus (Production c) (Production c)
  | Times (Production c) (Production c)
  | KleeneQ (Production c)
  | KleeneStar (Production c)
  | KleenePlus (Production c)
  deriving Show

makePrisms ''Production

production
  :: Grammatical p
  => p (Production Char) (Production Char)
production = production_
  where
    production_
      = ruleRec "production"
      $ \pro -> dichainl1 _Plus (sepBy "|") (series pro)
    series pro
      = rule "series"
      $ dichainl1 _Times (sepBy " ") (expression pro)
    expression pro
      = rule "expression"
      $ anyChar
      <|> nonterminal
      <|> terminal
      <|> mapPrism _KleeneQ ("(" >* pro *< ")?")
      <|> mapPrism _KleeneStar ("(" >* pro *< ")*")
      <|> mapPrism _KleenePlus ("(" >* pro *< ")+")
      <|> "(" >* pro *< ")"
    anyChar
      = rule "any-token"
      . mapPrism _AnyToken
      $ "<any-token>"
    terminal
      = rule "terminal"
      . mapPrism _Terminal
      $ "\"" >* manyP unreserved *< "\""
    nonterminal
      = rule "nonterminal"
      . mapPrism _NonTerminal
      $ "<" >* manyP unreserved *< ">"
    unreserved
      = rule "unreserved"
      . satisfy
      $ \ch -> ch `notElem` reserved
    reserved :: String = "\"<>|=()"

-- instance Show (Production Char) where
--   show prod = maybe (error "bad production") id
--     (runShowSyntax production prod)

data Grammar c a b = Grammar (Production c) [(String, Production c)]
  deriving Show
makePrisms ''Grammar
instance Functor (Grammar c a) where fmap = rmap
instance Applicative (Grammar c a) where
  pure _ = Grammar (Terminal []) []
  Grammar (Terminal []) rules0 <*> Grammar s1 rules1 =
    Grammar s1 (rules0 <> rules1)
  Grammar s0 rules0 <*> Grammar (Terminal []) rules1 =
    Grammar s0 (rules0 <> rules1)
  Grammar s0 rules0 <*> Grammar s1 rules1 =
    Grammar (Times s0 s1) (rules0 <> rules1)
instance Alternative (Grammar c a) where
  empty = Grammar Zero []
  Grammar Zero rules0 <|> Grammar s1 rules1 =
    Grammar s1 (rules0 <> rules1)
  Grammar s0 rules0 <|> Grammar Zero rules1 =
    Grammar s0 (rules0 <> rules1)
  Grammar s0 rules0 <|> Grammar s1 rules1 =
    Grammar (Plus s0 s1) (rules0 <> rules1)
  many (Grammar s rules) = Grammar (KleeneStar s) rules
  some (Grammar s rules) = Grammar (KleenePlus s) rules
instance Filterable (Grammar c a) where
  mapMaybe = dimapMaybe Just
instance Profunctor (Grammar c) where
  dimap _ _ = coerce
instance Distributor (Grammar c) where
  zeroP = Grammar Zero []
  Grammar Zero rules0 >+< Grammar s1 rules1 =
    Grammar s1 (rules0 <> rules1)
  Grammar s0 rules0 >+< Grammar Zero rules1 =
    Grammar s0 (rules0 <> rules1)
  Grammar s0 rules0 >+< Grammar s1 rules1 =
    Grammar (Plus s0 s1) (rules0 <> rules1)
  optionalP (Grammar s rules) = Grammar (KleeneQ s) rules
  manyP (Grammar start rules) = Grammar (KleeneStar start) rules
instance Choice (Grammar c) where
  left' = coerce
  right' = coerce
instance Cochoice (Grammar c) where
  unleft = coerce
  unright = coerce
instance Alternator (Grammar c) where
  alternate = either coerce coerce
  someP (Grammar start rules) = Grammar (KleenePlus start) rules
instance Filtrator (Grammar c) where
  filtrate g = (coerce g, coerce g)
instance Tokenized c c (Grammar c) where
  anyToken = Grammar AnyToken []
instance u ~ () => IsString (Grammar Char () u) where
  fromString str = Grammar (Terminal str) []
instance Regular (Grammar Char) where
  char ch = Grammar (Terminal [ch]) []
instance Grammatical (Grammar Char) where
  rule name (Grammar prod rules) = Grammar (NonTerminal name) ((name, prod) : rules)
  ruleRec name f =
    let Grammar prod rules = f (Grammar (NonTerminal name) [])
    in Grammar (NonTerminal name) ((name, prod) : rules)

grammar :: Grammatical p => p (Grammar Char a b) (Grammar Char a b)
grammar = grammar_
  where
    grammar_
      = rule "grammar"
      $ mapPrism _Grammar (start >*< manyP ("\n" >* rule_))
    start
      = rule "start"
      $ production
    rule_
      = rule "rule"
      $ name >*< (" = " >* production)
    name
      = rule "name"
      $ manyP unreserved
    unreserved
      = rule "unreserved"
      . satisfy
      $ \ch -> ch `notElem` reserved
    reserved :: String = "\"<>|=()"

-- instance Show (Grammar Char a b) where
--   show gram = maybe (error "bad grammar") id
--     (runShowSyntax grammar gram)

-- data Summation
--   = Digit Int
--   | Add Summation Summation
-- makePrisms ''Summation

-- digit, summationL, summationR :: Syntax Char p => p Summation Summation
-- digit = (_Digit . iso chr ord) >?< char DecimalNumber
-- summationL = dichainl1 _Add (sepBy (" + ")) digit
-- summationR = dichainr1 _Add (sepBy (" + ")) digit
