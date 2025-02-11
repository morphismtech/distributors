module Text.Grammar.Distributor
  ( -- * Grammar
    Grammatical (..), Grammar, Gramarr
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
import Text.ParserCombinators.ReadP (ReadP, get, readP_to_S)
import Witherable

class
  ( Alternator p
  , Filtrator p
  , Tokenized Char Char p
  , forall t. t ~ p () () => IsString t
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

type Gramarr a b = forall p. Grammatical p => p a a -> p b b

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
  = Terminal String -- ^ @abc123etc\.@
  | Sequence RegEx RegEx -- ^ @xy@
  | Fail
  | Alternate RegEx RegEx -- ^ @x|y@
  | KleeneOpt RegEx -- ^ @x?@
  | KleeneStar RegEx -- ^ @x*@
  | KleenePlus RegEx -- ^ @x+@
  | Any -- ^ @.@
  | End -- ^ @$@
  | InClass String -- ^ @[abc]@
  | NotInClass String -- ^ @[^abc]@
  | InCategory GeneralCategory -- ^ @\\p{Lu}@
  | NonTerminal String -- ^ @\\r{rule-name}@
  deriving (Eq, Ord, Show)
makePrisms ''RegEx

(-*-), (|||) :: RegEx -> RegEx -> RegEx

Terminal "" -*- rex = rex
rex -*- Terminal "" = rex
Fail -*- _ = Fail
_ -*- Fail = Fail
Terminal str0 -*- Terminal str1 = Terminal (str0 <> str1)
KleeneStar rex0 -*- rex1 | rex0 == rex1 = plusK rex0
rex0 -*- KleeneStar rex1 | rex0 == rex1 = plusK rex0
rex0 -*- rex1 = Sequence rex0 rex1

KleenePlus rex ||| Terminal "" = starK rex
Terminal "" ||| KleenePlus rex = starK rex
rex ||| Terminal "" = optK rex
Terminal "" ||| rex = optK rex
rex ||| Fail = rex
Fail ||| rex = rex
rex0 ||| rex1 | rex0 == rex1 = rex0
rex0 ||| rex1 = Alternate rex0 rex1

optK, starK, plusK :: RegEx -> RegEx

optK Fail = Terminal ""
optK (Terminal "") = Terminal ""
optK (KleenePlus rex) = KleeneStar rex
optK rex = KleeneOpt rex

starK Fail = Terminal ""
starK (Terminal "") = Terminal ""
starK rex = KleeneStar rex

plusK Fail = Fail
plusK (Terminal "") = Terminal ""
plusK rex = KleenePlus rex

newtype DiRegEx a b = DiRegEx {regString :: RegEx}
instance Functor (DiRegEx a) where fmap = rmap
instance Applicative (DiRegEx a) where
  pure _ = DiRegEx (Terminal [])
  DiRegEx rex1 <*> DiRegEx rex2 = DiRegEx (rex1 -*- rex2)
instance Alternative (DiRegEx a) where
  empty = DiRegEx Fail
  DiRegEx rex1 <|> DiRegEx rex2 = DiRegEx (rex1 ||| rex2)
  many (DiRegEx regex) = DiRegEx (KleeneStar regex)
  some (DiRegEx regex) = DiRegEx (KleenePlus regex)
instance Filterable (DiRegEx a) where
  mapMaybe _ = coerce
instance Profunctor DiRegEx where
  dimap _ _ = coerce
instance Distributor DiRegEx where
  zeroP = DiRegEx Fail
  DiRegEx rex1 >+< DiRegEx rex2 = DiRegEx (rex1 ||| rex2)
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

anyG :: Grammar RegEx
anyG = rule "any" $ "." >* pure Any

endG :: Grammar RegEx
endG = rule "end" $ "$" >* pure End

reservedClass :: String
reservedClass = "$()*+.?[\\]^{|}"

literalG :: Grammar Char
literalG = rule "literal" $ notInClass reservedClass

reservedG :: Grammar Char
reservedG = inClass reservedClass

escapedG :: Grammar Char
escapedG = rule "escaped" $ "\\" >* reservedG

charG :: Grammar Char
charG = rule "char" $ literalG <|> escapedG

nonterminalG :: Grammar RegEx
nonterminalG = rule "nonterminal" $
  _NonTerminal >?< "\\r{" >* manyP charG *< "}"

inClassG :: Grammar RegEx
inClassG = rule "in-class" $
  _InClass >?< "[" >* manyP charG *< "]"

notInClassG :: Grammar RegEx
notInClassG = rule "not-in-class" $
  _NotInClass >?< "[^" >* manyP charG *< "]"

inCategoryG :: Grammar RegEx
inCategoryG = rule "in-category" $
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

terminalG :: Grammar RegEx
terminalG = rule "terminal" $
  _Terminal >?< someP charG

tokenG :: Grammar RegEx
tokenG = _Terminal . _Cons >?< charG >*< pure ""

parenG :: Gramarr RegEx RegEx
parenG regex = rule "parenthesized" $
  "(" >* regex *< ")"

atomG :: Gramarr RegEx RegEx
atomG regex = rule "atom" $ foldl (<|>) empty
  [ nonterminalG
  , inClassG
  , notInClassG
  , inCategoryG
  , tokenG
  , parenG regex
  , anyG
  , endG
  ]

kleeneOptG :: Gramarr RegEx RegEx
kleeneOptG regex = rule "kleene-optional" $
  _KleeneOpt >?< atomG regex *< "?"

kleeneStarG :: Gramarr RegEx RegEx
kleeneStarG regex = rule "kleene-star" $
  _KleeneStar >?< atomG regex *< "*"

kleenePlusG :: Gramarr RegEx RegEx
kleenePlusG regex = rule "kleene-plus" $
  _KleenePlus >?< atomG regex *< "+"

exprG :: Gramarr RegEx RegEx
exprG regex = rule "expression" $ foldl (<|>) empty
  [ terminalG
  , kleeneOptG regex
  , kleeneStarG regex
  , kleenePlusG regex
  , atomG regex
  ]

seqG :: Gramarr RegEx RegEx
seqG regex = rule "sequence" $
  chainl1 _Sequence (sepBy "") (exprG regex)

altG :: Gramarr RegEx RegEx
altG regex = rule "alternate" $
  chainl1 _Alternate (sepBy "|") (seqG regex)

regexGrammar :: Grammar RegEx
regexGrammar = ruleRec "regex" $ \regex -> altG regex
