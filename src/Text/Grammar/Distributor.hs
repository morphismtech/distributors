module Text.Grammar.Distributor
  ( -- * Grammar
    Grammatical (..), Grammar
    -- * Generators
  , genReadP, readGrammar
  , genShowS, showGrammar
  , genRegEx, genGrammar, printGrammar
    -- * RegEx
  , RegEx (..), regexGrammar, regexString
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.PartialIso
import Data.Char
import Data.Coerce
import Data.Foldable (for_)
import Data.Function
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Profunctor
import Data.Profunctor.Distributor
import Data.Set (Set)
import Data.Set qualified as Set
import Data.String
import Text.ParserCombinators.ReadP hiding (many, satisfy, char, sepBy)
import Witherable

class
  ( Alternator p
  , Filtrator p
  , Tokenized Char Char p
  , forall u v. ((u ~ (), v ~ ()) => IsString (p u v))
  ) => Grammatical p where
    inClass :: String -> p Char Char
    inClass str = satisfy $ \ch -> elem ch str
    notInClass :: String -> p Char Char
    notInClass str = satisfy $ \ch -> notElem ch str
    inCategory :: GeneralCategory -> p Char Char
    inCategory cat = satisfy $ \ch -> cat == generalCategory ch
    theEnd :: p () ()
    theEnd = endOfTokens
    rule :: String -> p a b -> p a b
    rule _ = id
    ruleRec :: String -> (p a b -> p a b) -> p a b
    ruleRec name = rule name . fix

type Grammar a = forall p. Grammatical p => p a a

newtype DiShow a b = DiShow (a -> Maybe ShowS)
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
  fromString = tokens
instance Grammatical DiShow

newtype DiRead a b = DiRead (ReadP b)
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
instance Grammatical DiRead
instance u ~ () => IsString (DiRead () u) where
  fromString = tokens

data RegEx
  = Fail
  | Terminal String -- ^ abc123etc\.
  | Any -- ^ .
  | End -- ^ $
  | NonTerminal String -- ^ \r{rule-name}
  | InClass String -- ^ [abc]
  | NotInClass String -- ^ [^abc]
  | InCategory GeneralCategory -- ^ \p{Lu}
  | Alternate RegEx RegEx -- ^ p|q
  | Sequence RegEx RegEx -- ^ pq
  | KleeneOpt RegEx -- ^ p?
  | KleeneStar RegEx -- ^ p*
  | KleenePlus RegEx -- ^ p+
  deriving (Eq, Ord, Show)
makePrisms ''RegEx

newtype DiRegEx a b = DiRegEx {regString :: RegEx}
instance Functor (DiRegEx a) where fmap = rmap
instance Applicative (DiRegEx a) where
  pure _ = DiRegEx (Terminal [])
  DiRegEx (Terminal []) <*> regex = coerce regex
  regex <*> DiRegEx (Terminal []) = coerce regex
  DiRegEx regex1 <*> DiRegEx (KleeneStar regex2) =
    if regex1 == regex2
    then DiRegEx (KleenePlus regex1)
    else DiRegEx (Sequence regex1 (KleeneStar regex2))
  DiRegEx (KleeneStar regex1) <*> DiRegEx regex2 =
    if regex1 == regex2
    then DiRegEx (KleenePlus regex1)
    else DiRegEx (Sequence (KleeneStar regex1) regex2)
  DiRegEx (Terminal str0)
    <*> DiRegEx (Terminal str1) =
      DiRegEx (Terminal (str0 <> str1))
  DiRegEx regex1 <*> DiRegEx regex2 =
    DiRegEx (Sequence regex1 regex2)
instance Alternative (DiRegEx a) where
  empty = DiRegEx Fail
  DiRegEx Fail <|> regex = regex
  regex <|> DiRegEx Fail = regex
  DiRegEx (Terminal "") <|> DiRegEx (KleenePlus regex) =
    DiRegEx (KleeneStar regex)
  DiRegEx (KleenePlus regex) <|> DiRegEx (Terminal "") =
    DiRegEx (KleeneStar regex)
  DiRegEx (Terminal "") <|> DiRegEx regex = DiRegEx (KleeneOpt regex)
  DiRegEx regex <|> DiRegEx (Terminal "") = DiRegEx (KleeneOpt regex)
  DiRegEx regex1 <|> DiRegEx regex2 =
    DiRegEx (Alternate regex1 regex2)
  many (DiRegEx regex) = DiRegEx (KleeneStar regex)
  some (DiRegEx regex) = DiRegEx (KleenePlus regex)
instance Filterable (DiRegEx a) where
  mapMaybe _ = coerce
instance Profunctor DiRegEx where
  dimap _ _ = coerce
instance Distributor DiRegEx where
  zeroP = DiRegEx Fail
  DiRegEx Fail >+< DiRegEx regex = DiRegEx regex
  DiRegEx regex >+< DiRegEx Fail = DiRegEx regex
  DiRegEx (Terminal "") >+< DiRegEx (KleenePlus regex) =
    DiRegEx (KleeneStar regex)
  DiRegEx (KleenePlus regex) >+< DiRegEx (Terminal "") =
    DiRegEx (KleeneStar regex)
  DiRegEx (Terminal "") >+< DiRegEx regex = DiRegEx (KleeneOpt regex)
  DiRegEx regex >+< DiRegEx (Terminal "") = DiRegEx (KleeneOpt regex)
  DiRegEx regex1 >+< DiRegEx regex2 =
    DiRegEx (Alternate regex1 regex2)
  optionalP (DiRegEx (KleenePlus regex)) = DiRegEx (KleeneStar regex)
  optionalP (DiRegEx regex) = DiRegEx (KleeneOpt regex)
  manyP (DiRegEx regex) = DiRegEx (KleeneStar regex)
instance Choice DiRegEx where
  left' = coerce
  right' = coerce
instance Cochoice DiRegEx where
  unleft = coerce
  unright = coerce
instance Alternator DiRegEx where
  someP (DiRegEx regex) = DiRegEx (KleenePlus regex)
instance Filtrator DiRegEx
instance Tokenized Char Char DiRegEx where
  anyToken = DiRegEx Any
instance u ~ () => IsString (DiRegEx () u) where
  fromString str = DiRegEx (Terminal str)
instance Grammatical DiRegEx where
  inClass str = DiRegEx (InClass str)
  notInClass str = DiRegEx (NotInClass str)
  inCategory str = DiRegEx (InCategory str)
  theEnd = DiRegEx End

data DiGrammar a b = DiGrammar
  { grammarStart :: DiRegEx a b
  , grammarRules :: Map String (Set RegEx)
  }
instance Functor (DiGrammar a) where fmap = rmap
instance Applicative (DiGrammar a) where
  pure b = DiGrammar (pure b) mempty
  DiGrammar start1 rules1 <*> DiGrammar start2 rules2 =
    DiGrammar (start1 <*> start2) (Map.unionWith Set.union rules1 rules2)
instance Alternative (DiGrammar a) where
  empty = DiGrammar empty mempty
  DiGrammar start1 rules1 <|> DiGrammar start2 rules2 =
    DiGrammar (start1 <|> start2) (Map.unionWith Set.union rules1 rules2)
  many (DiGrammar start rules) = DiGrammar (many start) rules
  some (DiGrammar start rules) = DiGrammar (some start) rules
instance Filterable (DiGrammar a) where
  mapMaybe f (DiGrammar start rules) =
    DiGrammar (mapMaybe f start) rules
instance Profunctor DiGrammar where
  dimap f g (DiGrammar start rules) =
    DiGrammar (dimap f g start) rules
instance Distributor DiGrammar where
  zeroP = DiGrammar zeroP mempty
  DiGrammar start1 rules1 >+< DiGrammar start2 rules2 =
    DiGrammar (start1 >+< start2) (Map.unionWith Set.union rules1 rules2)
  optionalP (DiGrammar start rules) =
    DiGrammar (optionalP start) rules
  manyP (DiGrammar start rules) =
    DiGrammar (manyP start) rules
instance Choice DiGrammar where
  left' = coerce
  right' = coerce
instance Cochoice DiGrammar where
  unleft = coerce
  unright = coerce
instance Alternator DiGrammar where
  someP (DiGrammar start rules) =
    DiGrammar (someP start) rules
instance Filtrator DiGrammar
instance Tokenized Char Char DiGrammar where
  anyToken = DiGrammar anyToken mempty
instance u ~ () => IsString (DiGrammar () u) where
  fromString str = DiGrammar (fromString str) mempty
instance Grammatical DiGrammar where
  inClass str = DiGrammar (inClass str) mempty
  notInClass str = DiGrammar (notInClass str) mempty
  inCategory str = DiGrammar (inCategory str) mempty
  rule name gram = 
    let
      start = DiRegEx (NonTerminal name)
      newRule = Set.singleton (regString (grammarStart gram))
      rules = Map.insertWith Set.union name newRule (grammarRules gram)
    in
      DiGrammar start rules
  ruleRec name f =
    let
      matchRule = DiRegEx (NonTerminal name)
      gram = f (DiGrammar matchRule mempty)
      start = DiRegEx (NonTerminal name)
      newRule = Set.singleton (regString (grammarStart gram))
      rules = Map.insertWith Set.union name newRule (grammarRules gram)
    in
      DiGrammar start rules

genReadP :: Grammar a -> ReadP a
genReadP (DiRead p) = p

readGrammar :: Grammar a -> String -> [a]
readGrammar grammar str =
  [ a
  | (a, remaining) <- readP_to_S (genReadP grammar) str
  , remaining == []
  ]

genShowS :: Grammar a -> a -> Maybe ShowS
genShowS (DiShow p) = p

showGrammar :: Grammar a -> a -> Maybe String
showGrammar grammar a = ($ "") <$> genShowS grammar a

regexString :: RegEx -> String
regexString rex = maybe badRegex id stringMaybe
  where
    badRegex = "RegEx failed to print. " <> show rex
    stringMaybe = case regexGrammar of DiShow sh -> ($ "") <$> sh rex

genRegEx :: Grammar a -> RegEx
genRegEx (DiRegEx rex) = rex

genGrammar :: Grammar a -> [(String, RegEx)]
genGrammar (DiGrammar (DiRegEx start) rules) = ("start", start) :
  [ (name_i, rule_j)
  | (name_i, rules_i) <- Map.toList rules
  , rule_j <- Set.toList rules_i
  ]

printGrammar :: Grammar a -> IO ()
printGrammar gram = for_ (genGrammar gram) $ \(name_i, rule_i) -> do
  putStr name_i
  putStr " = "
  putStrLn (regexString rule_i)

anyP :: Grammatical p => p RegEx RegEx
anyP = rule "any" $ "." >* pure Any

endP :: Grammatical p => p RegEx RegEx
endP = rule "end" $ "$" >* pure End

reservedClass :: String
reservedClass = "$()*+.?[\\]^{|}"

literalP :: Grammatical p => p Char Char
literalP = rule "literal" $ notInClass reservedClass

reservedP :: Grammatical p => p Char Char
reservedP = inClass reservedClass

escapedP :: Grammatical p => p Char Char
escapedP = rule "escaped" $ "\\" >* reservedP

charP :: Grammatical p => p Char Char
charP = rule "char" $ literalP <|> escapedP

nonterminalP :: Grammatical p => p RegEx RegEx
nonterminalP = rule "nonterminal" $
  _NonTerminal >?< "\\r{" >* manyP charP *< "}"

inClassP :: Grammatical p => p RegEx RegEx
inClassP = rule "in-class" $
  _InClass >?< "[" >* manyP charP *< "]"

notInClassP :: Grammatical p => p RegEx RegEx
notInClassP = rule "not-in-class" $
  _NotInClass >?< "[^" >* manyP charP *< "]"

inCategoryP :: Grammatical p => p RegEx RegEx
inCategoryP = rule "in-category" $
  _InCategory >?< "\\p{" >* genCat *< "}" where
    genCat = foldl (<|>) empty
      [ "Lu" >* pure UppercaseLetter
      , "Ll" >* pure LowercaseLetter
      , "Lt" >* pure TitlecaseLetter
      , "Lm" >* pure ModifierLetter
      , "Lo" >* pure OtherLetter
      , "Mn" >* pure NonSpacingMark
      , "Mc" >* pure SpacingCombiningMark
      , "Me" >* pure EnclosingMark
      , "Nd" >* pure DecimalNumber
      , "Nl" >* pure LetterNumber
      , "No" >* pure OtherNumber
      , "Pc" >* pure ConnectorPunctuation
      , "Pd" >* pure DashPunctuation
      , "Ps" >* pure OpenPunctuation
      , "Pe" >* pure ClosePunctuation
      , "Pi" >* pure InitialQuote
      , "Pf" >* pure FinalQuote
      , "Po" >* pure OtherPunctuation
      , "Sm" >* pure MathSymbol
      , "Sc" >* pure CurrencySymbol
      , "Sk" >* pure ModifierSymbol
      , "So" >* pure OtherSymbol
      , "Zs" >* pure Space
      , "Zl" >* pure LineSeparator
      , "Zp" >* pure ParagraphSeparator
      , "Cc" >* pure Control
      , "Cf" >* pure Format
      , "Cs" >* pure Surrogate
      , "Co" >* pure PrivateUse
      , "Cn" >* pure NotAssigned
      ]

terminalP :: Grammatical p => p RegEx RegEx
terminalP = rule "terminal" $
  _Terminal >?< someP charP

tokenP :: Grammatical p => p RegEx RegEx
tokenP = _Terminal . _Cons >?< charP >*< pure ""

parenP :: Grammatical p => p RegEx RegEx -> p RegEx RegEx
parenP regex = rule "parenthesized" $
  "(" >* regex *< ")"

atomP :: Grammatical p => p RegEx RegEx -> p RegEx RegEx
atomP regex = rule "atom" $ foldl (<|>) empty
  [ nonterminalP
  , inClassP
  , notInClassP
  , inCategoryP
  , tokenP
  , parenP regex
  , anyP
  , endP
  ]

kleeneOptP :: Grammatical p => p RegEx RegEx -> p RegEx RegEx
kleeneOptP regex = rule "kleene-optional" $
  _KleeneOpt >?< atomP regex *< "?"

kleeneStarP :: Grammatical p => p RegEx RegEx -> p RegEx RegEx
kleeneStarP regex = rule "kleene-star" $
  _KleeneStar >?< atomP regex *< "*"

kleenePlusP :: Grammatical p => p RegEx RegEx -> p RegEx RegEx
kleenePlusP regex = rule "kleene-plus" $
  _KleenePlus >?< atomP regex *< "+"

exprP :: Grammatical p => p RegEx RegEx -> p RegEx RegEx
exprP regex = rule "expression" $ foldl (<|>) empty
  [ terminalP
  , kleeneOptP regex
  , kleeneStarP regex
  , kleenePlusP regex
  , atomP regex
  ]

seqP :: Grammatical p => p RegEx RegEx -> p RegEx RegEx
seqP regex = rule "sequence" $
  dichainl1 _Sequence (sepBy "") (exprP regex)

altP :: Grammatical p => p RegEx RegEx -> p RegEx RegEx
altP regex = rule "alternate" $
  dichainl1 _Alternate (sepBy "|") (seqP regex)

regexGrammar :: Grammar RegEx
regexGrammar = ruleRec "regex" $ \regex -> altP regex
