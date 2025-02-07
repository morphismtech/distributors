module Text.Grammar.Distributor
  ( Regular (..)
  , Grammatical (..)
  , DiRead (..), runDiRead, diRead
  , DiShow (..), runDiShow, diShow
  , ProdStr (..), prodP
  , Grammar (..), grammarP
  ) where

import Control.Applicative
import Control.Lens
-- import Control.Lens.Bifocal
import Control.Lens.PartialIso
import Control.Lens.Token
import Data.Char
import Data.Coerce
import Data.Foldable (for_)
import Data.Function
import qualified Data.Map as Map
import Data.Map (Map)
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

newtype DiShow a b = DiShow {unDiShow :: a -> Maybe ShowS}
instance Profunctor DiShow where
  dimap f _ (DiShow sh) = DiShow (sh . f)
instance Functor (DiShow a) where fmap = rmap
instance Applicative (DiShow a) where
  pure _ = DiShow (const (Just id))
  DiShow sh0 <*> DiShow sh1 =
    DiShow (liftA2 (liftA2 (.)) sh0 sh1)
instance Alternative (DiShow a) where
  empty = DiShow (const Nothing)
  DiShow sh0 <|> DiShow sh1 =
    DiShow (liftA2 (<|>) sh0 sh1)
  many (DiShow sh) = DiShow sh
  some (DiShow sh) = DiShow sh
instance Choice DiShow where
  left' (DiShow sh) =
    DiShow (either sh (const Nothing))
  right' (DiShow sh) =
    DiShow (either (const Nothing) sh)
instance Cochoice DiShow where
  unleft (DiShow sh) = DiShow (sh . Left)
  unright (DiShow sh) = DiShow (sh . Right)
instance Distributor DiShow where
  manyP (DiShow sh) = DiShow shmany where
    shmany str =
      foldl (liftA2 (.)) (pure id) (map sh str)
instance Alternator DiShow where
  someP (DiShow sh) = DiShow shsome where
    shsome str = do
      _ <- uncons str
      foldl (liftA2 (.)) (pure id) (map sh str)
instance Filtrator DiShow
instance Filterable (DiShow a) where
  mapMaybe = dimapMaybe Just
instance Tokenized Char Char DiShow where
  anyToken = DiShow (Just . (:))
instance u ~ () => IsString (DiShow () u) where
  fromString = fromChars
instance Regular DiShow
instance Grammatical DiShow

newtype DiRead a b = DiRead {unDiRead :: ReadP b}
instance Profunctor DiRead where
  dimap _ g (DiRead rd) = DiRead (g <$> rd)
instance Functor (DiRead a) where fmap = rmap
instance Applicative (DiRead a) where
  pure b = DiRead (pure b)
  DiRead rd0 <*> DiRead rd1 =
    DiRead (rd0 <*> rd1)
instance Alternative (DiRead a) where
  empty = DiRead empty
  DiRead rd0 <|> DiRead rd1 =
    DiRead (rd0 <|> rd1)
  many (DiRead rd) = DiRead (many rd)
  some (DiRead rd) = DiRead (some rd)
instance Choice DiRead where
  left' (DiRead rd) =
    DiRead (Left <$> rd)
  right' (DiRead rd) =
    DiRead (Right <$> rd)
instance Cochoice DiRead where
  unleft (DiRead rd) =
    DiRead (rd >>= either pure (const empty))
  unright (DiRead rd) =
    DiRead (rd >>= either (const empty) pure)
instance Distributor DiRead where
  manyP (DiRead rd) = DiRead (many rd)
instance Alternator DiRead where
  someP (DiRead rd) = DiRead (some rd)
instance Filtrator DiRead
instance Filterable (DiRead a) where
  mapMaybe = dimapMaybe Just
instance Tokenized Char Char DiRead where
  anyToken = DiRead get
instance Regular DiRead
instance Grammatical DiRead
instance u ~ () => IsString (DiRead () u) where
  fromString = fromChars

runDiRead :: DiRead a b -> String -> [(b, String)]
runDiRead (DiRead rd) str = readP_to_S rd str

runDiShow :: DiShow a b -> a -> Maybe String
runDiShow (DiShow sh) a = ($ "") <$> sh a

diShow :: Show a => DiShow a a
diShow = DiShow (Just . shows)

diRead :: Read a => DiRead a a
diRead = DiRead (readS_to_P reads)

data ProdStr
  = AnyToken -- ^ .
  | Zero -- ^ <start>
  | GenCat GeneralCategory
  | NonTerminal String -- ^ <rule-name>
  | Terminal String -- ^ abc123etc
  | Times ProdStr ProdStr -- ^ pq
  | Plus ProdStr ProdStr -- ^ p|q
  | KleeneOpt ProdStr -- ^ p?
  | KleeneStar ProdStr -- ^ p*
  | KleenePlus ProdStr -- ^ p+
  | Filtered ProdStr -- ^ p!
  deriving (Show, Read)
makePrisms ''ProdStr

reservedChars :: String
reservedChars = ".<>()|?*+!~"

escaped :: Iso' String String
escaped = iso unescape (>>= escape)

escape :: Char -> String
escape '.' = "\\."
escape '{' = "\\{"
escape '}' = "\\}"
escape '(' = "\\("
escape ')' = "\\)"
escape '|' = "\\|"
escape '?' = "\\?"
escape '*' = "\\*"
escape '+' = "\\+"
escape '!' = "\\x21"
escape '~' = "\\x7e"
escape '\\' = "\\\\"
escape c = [c]

unescape :: String -> String
unescape "" = ""
unescape ('\\':'.':cs) = '.' : unescape cs
unescape ('\\':'<':cs) = '<' : unescape cs
unescape ('\\':'>':cs) = '>' : unescape cs
unescape ('\\':'(':cs) = '(' : unescape cs
unescape ('\\':')':cs) = ')' : unescape cs
unescape ('\\':'|':cs) = '|' : unescape cs
unescape ('\\':'?':cs) = '?' : unescape cs
unescape ('\\':'*':cs) = '*' : unescape cs
unescape ('\\':'+':cs) = '+' : unescape cs
unescape ('\\':'x':'2':'1':cs) = '!' : unescape cs
unescape ('\\':'x':'7':'e':cs) = '~' : unescape cs
unescape ('\\':'\\':cs) = '\\' : unescape cs
unescape (c:cs) = c : unescape cs

unreservedP :: Grammatical p => p Char Char
unreservedP = satisfy $ \ch -> notElem ch reservedChars

terminalP :: Grammatical p => p ProdStr ProdStr
terminalP = rule "terminal" $
  _Terminal >?< manyP unreservedP

tokenP :: Grammatical p => p ProdStr ProdStr
tokenP = rule "char" $
  _Terminal . _Cons >?< unreservedP >*< pure ""

nonterminalP :: Grammatical p => p ProdStr ProdStr
nonterminalP = rule "nonterminal" $
  _NonTerminal >?< "<" >* manyP unreservedP *< ">"

anyP :: Grammatical p => p ProdStr ProdStr
anyP = rule "any" $ _AnyToken >?< "."

parenP :: Grammatical p => p ProdStr ProdStr -> p ProdStr ProdStr
parenP prod = rule "parenthesized" $ "(" >* prod *< ")"

atomP :: Grammatical p => p ProdStr ProdStr -> p ProdStr ProdStr
atomP prod = rule "atom" $
  tokenP <|> nonterminalP <|> anyP <|> parenP prod

kleeneOptP :: Grammatical p => p ProdStr ProdStr -> p ProdStr ProdStr
kleeneOptP prod = rule "kleene-optional" $
  _KleeneOpt >?< atomP prod *< "?"

kleeneStarP :: Grammatical p => p ProdStr ProdStr -> p ProdStr ProdStr
kleeneStarP prod = rule "kleene-star" $
  _KleeneStar >?< atomP prod *< "*"

kleenePlusP :: Grammatical p => p ProdStr ProdStr -> p ProdStr ProdStr
kleenePlusP prod = rule "kleene-plus" $
  _KleenePlus >?< atomP prod *< "+"

filteredP :: Grammatical p => p ProdStr ProdStr -> p ProdStr ProdStr
filteredP prod = rule "filtered" $
  _Filtered >?< atomP prod *< "!"

exprP :: Grammatical p => p ProdStr ProdStr -> p ProdStr ProdStr
exprP prod = rule "expression" $ asum @[]
  [ kleeneOptP prod
  , kleeneStarP prod
  , kleenePlusP prod
  , filteredP prod
  , nonterminalP
  , terminalP
  ]

seqP :: Grammatical p => p ProdStr ProdStr -> p ProdStr ProdStr
seqP prod = rule "sequence" $
  dichainr1 _Times (sepBy "") (exprP prod)

altP :: Grammatical p => p ProdStr ProdStr -> p ProdStr ProdStr
altP prod = rule "alternate" $
  dichainl1 _Plus (sepBy "|") (seqP prod)

empty0P :: Grammatical p => p ProdStr ProdStr
empty0P = rule "empty-language" $
  _Zero >?< "~"

empty1P :: Grammatical p => p ProdStr ProdStr
empty1P = rule "empty-string" $ _Terminal >?< pure ""

prodP :: Grammatical p => p ProdStr ProdStr
prodP = ruleRec "production" $ \prod ->
  empty0P <|> empty1P <|> altP prod

-- instance Show ProdStr where
--   show prod = maybe (error "bad production") id
--     (runDiShow production prod)

data Grammar a b = Grammar ProdStr (Map String ProdStr)
  deriving Show
makePrisms ''Grammar
instance Functor (Grammar a) where fmap = rmap
instance Applicative (Grammar a) where
  pure _ = Grammar (Terminal []) []
  Grammar (Terminal []) rules0 <*> Grammar s1 rules1 =
    Grammar s1 (rules0 <> rules1)
  Grammar s0 rules0 <*> Grammar (Terminal []) rules1 =
    Grammar s0 (rules0 <> rules1)
  Grammar (Terminal str0) rules0
    <*> Grammar (Terminal str1) rules1 =
      Grammar (Terminal (str0 <> str1)) (rules0 <> rules1)
  Grammar s0 rules0 <*> Grammar s1 rules1 =
    Grammar (Times s0 s1) (rules0 <> rules1)
instance Alternative (Grammar a) where
  empty = Grammar Zero []
  Grammar Zero rules0 <|> Grammar s1 rules1 =
    Grammar s1 (rules0 <> rules1)
  Grammar s0 rules0 <|> Grammar Zero rules1 =
    Grammar s0 (rules0 <> rules1)
  Grammar s0 rules0 <|> Grammar s1 rules1 =
    Grammar (Plus s0 s1) (rules0 <> rules1)
  many (Grammar s rules) = Grammar (KleeneStar s) rules
  some (Grammar s rules) = Grammar (KleenePlus s) rules
instance Filterable (Grammar a) where
  mapMaybe = dimapMaybe Just
instance Profunctor Grammar where
  dimap _ _ = coerce
instance Distributor Grammar where
  zeroP = Grammar Zero []
  Grammar Zero rules0 >+< Grammar s1 rules1 =
    Grammar s1 (rules0 <> rules1)
  Grammar s0 rules0 >+< Grammar Zero rules1 =
    Grammar s0 (rules0 <> rules1)
  Grammar s0 rules0 >+< Grammar s1 rules1 =
    Grammar (Plus s0 s1) (rules0 <> rules1)
  optionalP (Grammar s rules) = Grammar (KleeneOpt s) rules
  manyP (Grammar start rules) = Grammar (KleeneStar start) rules
instance Choice Grammar where
  left' (Grammar (Filtered p) rules) = Grammar (Filtered p) (rules)
  left' (Grammar p rules) = Grammar (Filtered p) rules
  right' (Grammar (Filtered p) rules) = Grammar (Filtered p) (rules)
  right' (Grammar p rules) = Grammar (Filtered p) rules
instance Cochoice Grammar where
  unleft = coerce
  unright = coerce
instance Alternator Grammar where
  someP (Grammar start rules) = Grammar (KleenePlus start) rules
instance Filtrator Grammar
instance Tokenized Char Char Grammar where
  anyToken = Grammar AnyToken []
instance u ~ () => IsString (Grammar () u) where
  fromString str = Grammar (Terminal str) []
instance Regular Grammar where
  char ch = Grammar (Terminal (escape ch)) []
instance Grammatical Grammar where
  rule name (Grammar prod rules) = Grammar (NonTerminal name) (Map.insert name prod rules)
  ruleRec name f =
    let Grammar prod rules = f (Grammar (NonTerminal name) [])
    in Grammar (NonTerminal name) (Map.insert name prod rules)

startP :: Grammatical p => p ProdStr ProdStr
startP = rule "start" $ "start = " >* prodP

ruleP :: Grammatical p => p (String, ProdStr) (String, ProdStr)
ruleP = rule "rule" $ manyP unreservedP >*< " = " >* prodP

grammarP :: Grammatical p => p (Grammar a b) (Grammar a b)
grammarP = rule "grammar" $
  _Grammar >?< startP >*< (iso Map.toList Map.fromList >?< manyP ("\n" >* ruleP))


gramma :: Grammar a b -> [(String, Maybe String)]
gramma (Grammar p ps) = [(name, runDiShow prodP q) | (name, q) <- ("start",p):Map.toList ps]

grampa :: Grammar a b -> IO ()
grampa g = for_ (gramma g) $ \(name, prodStrMay) -> do
  putStr name
  putStr " = "
  putStrLn (maybe "failing" id prodStrMay)
