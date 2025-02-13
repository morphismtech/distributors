{-|
Module      : Text.Grammar.Distributor
Description : grammars
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Text.Grammar.Distributor
  ( -- * Grammar
    Grammatical (..), Grammar, Grammarr
    -- * Generators
  , genReadS, readGrammar
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
import Data.Foldable
import Data.Function
import Data.Profunctor
import Data.Profunctor.Distributor
import Data.Set (Set, insert)
import Data.String
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

    rule :: String -> p a b -> p a b
    rule _ = id

    ruleRec :: String -> (p a b -> p a b) -> p a b
    ruleRec name = rule name . fix

instance (Alternative f, Cons s s Char Char)
  => Grammatical (Printor s f)
instance (Monad f, Alternative f, Filterable f, Cons s s Char Char)
  => Grammatical (Parsor s f)

type Grammar a = forall p. Grammatical p => p a a

type Grammarr a b = forall p. Grammatical p => p a a -> p b b

-- RegEx --

data RegEx
  = Terminal String -- ^ @abc123etc\\.@
  | Sequence RegEx RegEx -- ^ @xy@
  | Fail -- ^ @\\q@
  | Alternate RegEx RegEx -- ^ @x|y@
  | KleeneOpt RegEx -- ^ @x?@
  | KleeneStar RegEx -- ^ @x*@
  | KleenePlus RegEx -- ^ @x+@
  | AnyChar -- ^ @.@
  | InClass String -- ^ @[abc]@
  | NotInClass String -- ^ @[^abc]@
  | InCategory GeneralCategory -- ^ @\\p{Lu}@
  | NonTerminal String -- ^ @\\q{rule-name}@
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
optK (KleenePlus rex) = starK rex
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
  many (DiRegEx rex) = DiRegEx (KleeneStar rex)
  some (DiRegEx rex) = DiRegEx (KleenePlus rex)
instance Filterable (DiRegEx a) where
  mapMaybe _ = coerce
instance Profunctor DiRegEx where
  dimap _ _ = coerce
instance Distributor DiRegEx where
  zeroP = DiRegEx Fail
  DiRegEx rex1 >+< DiRegEx rex2 = DiRegEx (rex1 ||| rex2)
  optionalP (DiRegEx rex) = DiRegEx (optK rex)
  manyP (DiRegEx rex) = DiRegEx (starK rex)
instance Choice DiRegEx where
  left' = coerce
  right' = coerce
instance Cochoice DiRegEx where
  unleft = coerce
  unright = coerce
instance Alternator DiRegEx where
  someP (DiRegEx rex) = DiRegEx (plusK rex)
instance Filtrator DiRegEx
instance IsString (DiRegEx () ()) where
  fromString str = DiRegEx (Terminal str)
instance Tokenized Char Char DiRegEx where
  anyToken = DiRegEx AnyChar
instance Grammatical DiRegEx where
  inClass str = DiRegEx (InClass str)
  notInClass str = DiRegEx (NotInClass str)
  inCategory str = DiRegEx (InCategory str)

data DiGrammar a b = DiGrammar
  { grammarStart :: DiRegEx a b
  , grammarRules :: Set (String, RegEx)
  }
instance Functor (DiGrammar a) where fmap = rmap
instance Applicative (DiGrammar a) where
  pure b = DiGrammar (pure b) mempty
  DiGrammar start1 rules1 <*> DiGrammar start2 rules2 =
    DiGrammar (start1 <*> start2) (rules1 <> rules2)
instance Alternative (DiGrammar a) where
  empty = DiGrammar empty mempty
  DiGrammar start1 rules1 <|> DiGrammar start2 rules2 =
    DiGrammar (start1 <|> start2) (rules1 <> rules2)
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
    DiGrammar (start1 >+< start2) (rules1 <> rules2)
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
instance IsString (DiGrammar () ()) where
  fromString str = DiGrammar (fromString str) mempty
instance Tokenized Char Char DiGrammar where
  anyToken = DiGrammar anyToken mempty
instance Grammatical DiGrammar where
  inClass str = DiGrammar (inClass str) mempty
  notInClass str = DiGrammar (notInClass str) mempty
  inCategory str = DiGrammar (inCategory str) mempty
  rule name gram = 
    let
      start = DiRegEx (NonTerminal name)
      newRule = regString (grammarStart gram)
      rules = insert (name, newRule) (grammarRules gram)
    in
      DiGrammar start rules
  ruleRec name f =
    let
      matchRule = DiRegEx (NonTerminal name)
      gram = f (DiGrammar matchRule mempty)
      start = DiRegEx (NonTerminal name)
      newRule = regString (grammarStart gram)
      rules = insert (name, newRule) (grammarRules gram)
    in
      DiGrammar start rules

-- Generators --

genReadS :: Grammar a -> ReadS a
genReadS = runParsor

readGrammar :: Grammar a -> String -> [a]
readGrammar grammar str =
  [ a
  | (a, remaining) <- genReadS grammar str
  , remaining == []
  ]

genShowS :: Grammar a -> a -> Maybe ShowS
genShowS = runPrintor

showGrammar :: Grammar a -> a -> Maybe String
showGrammar grammar a = ($ "") <$> genShowS grammar a

regexString :: RegEx -> String
regexString rex = maybe badRegex id stringMaybe
  where
    badRegex = "RegEx failed to print. " <> show rex
    stringMaybe = case regexGrammar of Printor sh -> ($ "") <$> sh rex

genRegEx :: Grammar a -> RegEx
genRegEx (DiRegEx rex) = rex

genGrammar :: Grammar a -> [(String, RegEx)]
genGrammar (DiGrammar (DiRegEx start) rules) =
  ("start", start) : toList rules

printGrammar :: Grammar a -> IO ()
printGrammar gram = for_ (genGrammar gram) $ \(name_i, rule_i) -> do
  putStr name_i
  putStr " = "
  putStrLn (regexString rule_i)

-- Grammar RegEx --

{- |
>>> printGrammar regexGrammar
start = \r{regex}
alternate = \r{sequence}(\|\r{sequence})*
any = \.
atom = \r{nonterminal}|\r{in-class}|\r{not-in-class}|\r{in-category}|\r{char}|\r{parenthesized}|\r{any}
char = \r{literal}|\r{escaped}
escaped = \\[\$\(\)\*\+\.\?\[\\\]\^\{\|\}]
expression = \r{terminal}|\r{kleene-optional}|\r{kleene-star}|\r{kleene-plus}|\r{atom}
in-category = \\p\{(Lu|Ll|Lt|Lm|Lo|Mn|Mc|Me|Nd|Nl|No|Pc|Pd|Ps|Pe|Pi|Pf|Po|Sm|Sc|Sk|So|Zs|Zl|Zp|Cc|Cf|Cs|Co|Cn)\}
in-class = \[\r{char}*\]
kleene-optional = \r{atom}\?
kleene-plus = \r{atom}\+
kleene-star = \r{atom}\*
literal = [^\$\(\)\*\+\.\?\[\\\]\^\{\|\}]
nonterminal = \\r\{\r{char}*\}
not-in-class = \[\^\r{char}*\]
parenthesized = \(\r{regex}\)
regex = \r{alternate}
sequence = \r{expression}+
terminal = \r{char}+

-}
regexGrammar :: Grammar RegEx
regexGrammar = ruleRec "regex" $ \rex -> altG rex <|> failG

altG :: Grammarr RegEx RegEx
altG rex = rule "alternate" $
  chainl1 _Alternate (sepBy "|") (seqG rex)

anyG :: Grammar RegEx
anyG = rule "any" $ "." >* pure AnyChar

atomG :: Grammarr RegEx RegEx
atomG rex = rule "atom" $ foldl (<|>) empty
  [ nonterminalG
  , failG
  , inClassG
  , notInClassG
  , inCategoryG
  , tokenG
  , anyG
  , parenG rex
  ]

charG :: Grammar Char
charG = rule "char" $ literalG <|> escapedG

escapedG :: Grammar Char
escapedG = rule "escaped" $ "\\" >* inClass reservedClass

exprG :: Grammarr RegEx RegEx
exprG rex = rule "expression" $ foldl (<|>) empty
  [ terminalG
  , kleeneOptG rex
  , kleeneStarG rex
  , kleenePlusG rex
  , atomG rex
  ]

failG :: Grammar RegEx
failG = rule "fail" $ _Fail >?< "\\q"

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

inClassG :: Grammar RegEx
inClassG = rule "in-class" $
  _InClass >?< "[" >* manyP charG *< "]"

literalG :: Grammar Char
literalG = rule "literal" $ notInClass reservedClass

nonterminalG :: Grammar RegEx
nonterminalG = rule "nonterminal" $
  _NonTerminal >?< "\\q{" >* manyP charG *< "}"

notInClassG :: Grammar RegEx
notInClassG = rule "not-in-class" $
  _NotInClass >?< "[^" >* manyP charG *< "]"

reservedClass :: String
reservedClass = "$()*+.?[\\]^{|}"

terminalG :: Grammar RegEx
terminalG = rule "terminal" $
  _Terminal >?< someP charG

tokenG :: Grammar RegEx
tokenG = _Terminal >?< charG >:< pure ""

parenG :: Grammarr RegEx RegEx
parenG rex = rule "parenthesized" $
  "(" >* rex *< ")"

kleeneOptG :: Grammarr RegEx RegEx
kleeneOptG rex = rule "kleene-optional" $
  _KleeneOpt >?< atomG rex *< "?"

kleeneStarG :: Grammarr RegEx RegEx
kleeneStarG rex = rule "kleene-star" $
  _KleeneStar >?< atomG rex *< "*"

kleenePlusG :: Grammarr RegEx RegEx
kleenePlusG rex = rule "kleene-plus" $
  _KleenePlus >?< atomG rex *< "+"

seqG :: Grammarr RegEx RegEx
seqG rex = rule "sequence" $
  chainl1 _Sequence noSep (exprG rex)
