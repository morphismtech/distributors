module Text.Grammar.Distributor
  ( Regular (..)
  , Grammatical (..)
  , DiRead (..), runDiRead, diRead
  , DiShow (..), runDiShow, diShow
  , RegEx (..)
  , Grammar (..)
  , RegString (..)
  , RegMatch (..)
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.PartialIso
import Control.Lens.Token
import Data.Char
import Data.Coerce
import Data.Function
import Data.Map (Map, insert)
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
    inClass :: String -> p Char Char
    inClass str = satisfy $ \ch -> elem ch str
    notInClass :: String -> p Char Char
    notInClass str = satisfy $ \ch -> notElem ch str
    inCategory :: GeneralCategory -> p Char Char
    inCategory cat = satisfy $ \ch -> cat == generalCategory ch

fromChars :: Regular p => String -> p () ()
fromChars [] = oneP
fromChars (c:cs) = char c *> fromChars cs

class Regular p => Grammatical p where
  rule :: String -> p a b -> p a b
  rule name p = ruleRec name (const p)
  ruleRec :: String -> (p a b -> p a b) -> p a b
  ruleRec _ = fix

newtype DiShow c a b = DiShow {unDiShow :: a -> Maybe ([c] -> [c])}
instance Profunctor (DiShow c) where
  dimap f _ (DiShow sh) = DiShow (sh . f)
instance Functor (DiShow c a) where fmap = rmap
instance Applicative (DiShow c a) where
  pure _ = DiShow (const (Just id))
  DiShow sh0 <*> DiShow sh1 =
    DiShow (liftA2 (liftA2 (.)) sh0 sh1)
instance Alternative (DiShow c a) where
  empty = DiShow (const Nothing)
  DiShow sh0 <|> DiShow sh1 =
    DiShow (liftA2 (<|>) sh0 sh1)
  many (DiShow sh) = DiShow sh
  some (DiShow sh) = DiShow sh
instance Choice (DiShow c) where
  left' (DiShow sh) =
    DiShow (either sh (const Nothing))
  right' (DiShow sh) =
    DiShow (either (const Nothing) sh)
instance Cochoice (DiShow c) where
  unleft (DiShow sh) = DiShow (sh . Left)
  unright (DiShow sh) = DiShow (sh . Right)
instance Distributor (DiShow c) where
  manyP (DiShow sh) = DiShow shmany where
    shmany str =
      foldl (liftA2 (.)) (pure id) (map sh str)
instance Alternator (DiShow c) where
  someP (DiShow sh) = DiShow shsome where
    shsome str = do
      _ <- uncons str
      foldl (liftA2 (.)) (pure id) (map sh str)
instance Filtrator (DiShow c)
instance Filterable (DiShow c a) where
  mapMaybe = dimapMaybe Just
instance Tokenized c c (DiShow c) where
  anyToken = DiShow (Just . (:))
instance u ~ () => IsString (DiShow Char () u) where
  fromString = fromChars
instance Regular (DiShow Char)
instance Grammatical (DiShow Char)

-- newtype DiRead c a b = DiRead {unDiRead :: [c] -> [(b, [c])]}
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

runDiShow :: DiShow c a b -> a -> Maybe [c]
runDiShow (DiShow sh) a = ($ []) <$> sh a

diShow :: Show a => DiShow Char a a
diShow = DiShow (Just . shows)

diRead :: Read a => DiRead a a
diRead = DiRead (readS_to_P reads)

data RegMatch
  = Any -- ^ .
  | NonTerminal String -- ^ \r{rule-name}
  | InClass String -- ^ [abc]
  | NotInClass String -- ^ [^abc]
  | InCategory GeneralCategory -- ^ \p{Lu}
  deriving (Eq,Ord)
makePrisms ''RegMatch

data RegString
  = Fail
  | Terminal String -- ^ abc123etc\.
  | Match RegMatch
  | Alternate RegString RegString
  | Sequence RegString RegString
  | KleeneOpt RegString
  | KleeneStar RegString
  | KleenePlus RegString
  deriving (Eq, Ord)
makePrisms ''RegString

instance Show RegString where
  show regstr = maybe "fail" show (runDiShow regexP regstr)

newtype RegEx a b = RegEx {regString :: RegString}
  deriving stock (Eq, Ord)
  deriving newtype Show
instance Functor (RegEx a) where fmap = rmap
instance Applicative (RegEx a) where
  pure _ = RegEx (Terminal [])
  RegEx (Terminal []) <*> regex = coerce regex
  regex <*> RegEx (Terminal []) = coerce regex
  RegEx (Terminal str0)
    <*> RegEx (Terminal str1) =
      RegEx (Terminal (str0 <> str1))
  RegEx regex1 <*> RegEx regex2 =
    RegEx (Sequence regex1 regex2)
instance Alternative (RegEx a) where
  empty = RegEx Fail
  RegEx Fail <|> regex = regex
  regex <|> RegEx Fail = regex
  RegEx regex1 <|> RegEx regex2 =
    RegEx (Alternate regex1 regex2)
  many (RegEx regex) = RegEx (KleeneStar regex)
  some (RegEx regex) = RegEx (KleenePlus regex)
instance Filterable (RegEx a) where
  mapMaybe _ = coerce
instance Profunctor RegEx where
  dimap _ _ = coerce
instance Distributor RegEx where
  zeroP = RegEx Fail
  RegEx Fail >+< RegEx regex = RegEx regex
  RegEx regex >+< RegEx Fail = RegEx regex
  RegEx regex1 >+< RegEx regex2 =
    RegEx (Alternate regex1 regex2)
  optionalP (RegEx regex) = RegEx (KleeneOpt regex)
  manyP (RegEx regex) = RegEx (KleeneStar regex)
instance Choice RegEx where
  left' = coerce
  right' = coerce
instance Cochoice RegEx where
  unleft = coerce
  unright = coerce
instance Alternator RegEx where
  someP (RegEx regex) = RegEx (KleenePlus regex)
instance Filtrator RegEx
instance Tokenized Char Char RegEx where
  anyToken = RegEx (Match Any)
instance u ~ () => IsString (RegEx () u) where
  fromString str = RegEx (Terminal str)
instance Regular RegEx where
  char ch = RegEx (Terminal [ch])
  inClass str = RegEx (Match (InClass str))
  notInClass str = RegEx (Match (NotInClass str))
  inCategory str = RegEx (Match (InCategory str))
instance Grammatical RegEx

data Grammar a b = Grammar
  { grammarStart :: RegEx a b
  , grammarRules :: Map String RegString
  } deriving (Eq, Ord, Show)
instance Functor (Grammar a) where fmap = rmap
instance Applicative (Grammar a) where
  pure b = Grammar (pure b) mempty
  Grammar start1 rules1 <*> Grammar start2 rules2 =
    Grammar (start1 <*> start2) (rules1 <> rules2)
instance Alternative (Grammar a) where
  empty = Grammar empty mempty
  Grammar start1 rules1 <|> Grammar start2 rules2 =
    Grammar (start1 <|> start2) (rules1 <> rules2)
  many (Grammar start rules) = Grammar (many start) rules
  some (Grammar start rules) = Grammar (some start) rules
instance Filterable (Grammar a) where
  mapMaybe f (Grammar start rules) =
    Grammar (mapMaybe f start) rules
instance Profunctor Grammar where
  dimap f g (Grammar start rules) =
    Grammar (dimap f g start) rules
instance Distributor Grammar where
  zeroP = Grammar zeroP mempty
  Grammar start1 rules1 >+< Grammar start2 rules2 =
    Grammar (start1 >+< start2) (rules1 <> rules2)
  optionalP (Grammar start rules) =
    Grammar (optionalP start) rules
  manyP (Grammar start rules) =
    Grammar (manyP start) rules
instance Choice Grammar where
  left' = coerce
  right' = coerce
instance Cochoice Grammar where
  unleft = coerce
  unright = coerce
instance Alternator Grammar where
  someP (Grammar start rules) =
    Grammar (someP start) rules
instance Filtrator Grammar
instance Tokenized Char Char Grammar where
  anyToken = Grammar anyToken mempty
instance u ~ () => IsString (Grammar () u) where
  fromString str = Grammar (fromString str) mempty
instance Regular Grammar where
  char c = Grammar (char c) mempty
  inClass str = Grammar (inClass str) mempty
  notInClass str = Grammar (notInClass str) mempty
  inCategory str = Grammar (inCategory str) mempty
instance Grammatical Grammar where
  rule name gram = 
    let
      start = RegEx (Match (NonTerminal name))
      newRule = regString (grammarStart gram)
      rules = insert name newRule (grammarRules gram)
    in
      Grammar start rules
  ruleRec name f =
    let
      matchRule = RegEx (Match (NonTerminal name))
      gram = f (Grammar matchRule mempty)
      start = RegEx (Match (NonTerminal name))
      newRule = regString (grammarStart gram)
      rules = insert name newRule (grammarRules gram)
    in
      Grammar start rules

anyP :: Grammatical p => p RegMatch RegMatch
anyP = rule "any" $ char '.' >* pure Any

reservedClass :: String
reservedClass = "()*+.?[\\]^{|}"

unreservedP :: Grammatical p => p Char Char
unreservedP = notInClass reservedClass

reservedP :: Grammatical p => p Char Char
reservedP = inClass reservedClass

escapedP :: Grammatical p => p Char Char
escapedP = rule "escaped" $ char '\\' >* reservedP

charP :: Grammatical p => p Char Char
charP = rule "char" $ unreservedP <|> escapedP

nonterminalP :: Grammatical p => p RegMatch RegMatch
nonterminalP = rule "nonterminal" $
  _NonTerminal >?< "\\r{" >* manyP charP *< "}"

inClassP :: Grammatical p => p RegMatch RegMatch
inClassP = rule "in-class" $
  _InClass >?< "[" >* manyP charP *< "]"

notInClassP :: Grammatical p => p RegMatch RegMatch
notInClassP = rule "not-in-class" $
  _NotInClass >?< "[^" >* manyP charP *< "]"

-- inCategoryP :: Grammatical p => p RegMatch RegMatch
-- inCategoryP = rule "in-gen-cat" $
--   _InCategory >?< "\\p{" >* fromString (show )

matchP :: Grammatical p => p RegString RegString
matchP = rule "match" $ _Match >?< asum @[]
  [ nonterminalP
  , inClassP
  , notInClassP
  , anyP
  ]

terminalP :: Grammatical p => p RegString RegString
terminalP = rule "terminal" $
  _Terminal >?< manyP charP

tokenP :: Grammatical p => p RegString RegString
tokenP = _Terminal . _Cons >?< charP >*< pure ""

parenP :: Grammatical p => p RegString RegString -> p RegString RegString
parenP regex = rule "parenthesized" $
  char '(' >* regex *< char ')'

atomP :: Grammatical p => p RegString RegString -> p RegString RegString
atomP regex = rule "atom" $ tokenP <|> matchP <|> parenP regex

kleeneOptP :: Grammatical p => p RegString RegString -> p RegString RegString
kleeneOptP regex = rule "kleene-optional" $
  _KleeneOpt >?< atomP regex *< char '?'

kleeneStarP :: Grammatical p => p RegString RegString -> p RegString RegString
kleeneStarP regex = rule "kleene-star" $
  _KleeneStar >?< atomP regex *< char '*'

kleenePlusP :: Grammatical p => p RegString RegString -> p RegString RegString
kleenePlusP regex = rule "kleene-plus" $
  _KleenePlus >?< atomP regex *< char '+'

exprP :: Grammatical p => p RegString RegString -> p RegString RegString
exprP regex = rule "expression" $ asum @[]
  [ terminalP
  , kleeneOptP regex
  , kleeneStarP regex
  , kleenePlusP regex
  , atomP regex
  ]

seqP :: Grammatical p => p RegString RegString -> p RegString RegString
seqP regex = rule "sequence" $
  dichainr1 _Sequence (sepBy oneP) (exprP regex)

altP :: Grammatical p => p RegString RegString -> p RegString RegString
altP regex = rule "alternate" $
  dichainl1 _Alternate (sepBy (char ('|'))) (seqP regex)

regexP :: Grammatical p => p RegString RegString
regexP = ruleRec "regex" $ \regex -> altP regex
