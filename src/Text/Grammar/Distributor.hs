{-|
Module      : Text.Grammar.Distributor
Description : grammars
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable

See Joachim Breitner,
[Showcasing Applicative]
(https://www.joachim-breitner.de/blog/710-Showcasing_Applicative)
for idea to unify grammars.
-}

module Text.Grammar.Distributor
  ( -- * Grammar
    Grammar, Grammarr, Grammatical (..)
    -- * Generators
  , genReadS
  , readGrammar
  , genShowS
  , showGrammar
  , genRegEx
  , genGrammar
  , printGrammar
    -- * RegEx
  , RegEx (..)
  , normRegEx
  , regexString
  , stringRegEx
  , regexGrammar
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
import GHC.Generics
import Witherable

{- | `Grammar` is a Backus-Naur form grammar,
extended by regular expressions,
embedded in Haskell, with combinators:

* pattern matching `>?`, `>?<`
* alternation `<|>`
* sequencing `>*<`, `>*`, `*<`
* Kleene quantifiers `optionalP`, `manyP`, `someP`
* any character `anyToken`
* regular predicates `inClass`, `notInClass`, `inCategory`, `notInCategory`
* nonregular predicate `satisfy`
* terminal strings `tokens`, `fromString` and -XOverloadedStrings
* nonterminal rules `rule`, `ruleRec`
* and more.

To see an example of a `Grammar`, look at the source of `regexGrammar`.
-}
type Grammar a = forall p. Grammatical p => p a a

{- | A `Grammarr` is just a function of `Grammar`s,
useful for expressing one in terms of another `Grammar`.
The arr is for arrow; and it should be pronounced like a pirate.
-}
type Grammarr a b = forall p. Grammatical p => p a a -> p b b

{- | One can create new generators from a `Grammar` by defining
instances of `Grammatical`. For instance, one could create
generators for Parsec style parsers, and use `rule` for
labeling of parse errors.

A `Grammatical` `Profunctor` is a partial distributor,
being an `Alternator` & `Filtrator`.
It is also `Tokenized` with `Char` input & output tokens,
and `IsString` with the property:

prop> fromString = tokens

`Grammatical` has defaults for methods
`inClass`, `notInClass`, `inCategory`, `notInCategory`
in terms of `satisfy`;
and `rule` & `ruleRec` in terms of `id` & `fix`.
-}
class
  ( Alternator p
  , Filtrator p
  , Tokenized Char Char p
  , forall t. t ~ p () () => IsString t
  ) => Grammatical p where

    {- | Only characters which are in the given `String`.-}
    inClass :: String -> p Char Char
    inClass str = satisfy $ \ch -> elem ch str

    {- | Only characters which are not in the given `String`.-}
    notInClass :: String -> p Char Char
    notInClass str = satisfy $ \ch -> notElem ch str

    {- | Only characters which are in the given `GeneralCategory`.-}
    inCategory :: GeneralCategory -> p Char Char
    inCategory cat = satisfy $ \ch -> cat == generalCategory ch

    {- | Only characters which are not in the given `GeneralCategory`.-}
    notInCategory :: GeneralCategory -> p Char Char
    notInCategory cat = satisfy $ \ch -> cat /= generalCategory ch

    {- | A nonterminal rule. -}
    rule :: String -> p a a -> p a a
    rule _ = id

    {- | A recursive, nonterminal rule. -}
    ruleRec :: String -> (p a a -> p a a) -> p a a
    ruleRec name = rule name . fix

instance (Alternative f, Cons s s Char Char)
  => Grammatical (Printor s f)
instance (Monad f, Alternative f, Filterable f, Cons s s Char Char)
  => Grammatical (Parsor s f)

-- RegEx --

{- | A version of regular expressions extended by nonterminals. -}
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
  | NotInCategory GeneralCategory -- ^ @\\P{Ll}@
  | NonTerminal String -- ^ @\\q{rule-name}@
  deriving stock (Eq, Ord, Show, Generic)
makeNestedPrisms ''RegEx
makeNestedPrisms ''GeneralCategory

-- Kleene Star Algebra Operators

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

{- | Normalize a `RegEx`.

>>> normRegEx (Sequence (Terminal "abc") (Terminal "xyz"))
Terminal "abcxyz"
-}
normRegEx :: RegEx -> RegEx
normRegEx = \case
  Sequence rex0 rex1 -> normRegEx rex0 -*- normRegEx rex1
  Alternate rex0 rex1 -> normRegEx rex0 ||| normRegEx rex1
  KleeneOpt rex -> optK (normRegEx rex)
  KleeneStar rex -> starK (normRegEx rex)
  KleenePlus rex -> plusK (normRegEx rex)
  otherRegEx -> otherRegEx

-- RegEx generator

newtype DiRegEx a b = DiRegEx RegEx
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
  inCategory cat = DiRegEx (InCategory cat)
  notInCategory cat = DiRegEx (NotInCategory cat)

-- Grammar generator

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
      DiRegEx newRule = grammarStart gram
      rules = insert (name, newRule) (grammarRules gram)
    in
      DiGrammar start rules
  ruleRec name f =
    let
      start = DiRegEx (NonTerminal name)
      gram = f (DiGrammar start mempty)
      DiRegEx newRule = grammarStart gram
      rules = insert (name, newRule) (grammarRules gram)
    in
      DiGrammar start rules

-- Generators --

{- | Generate a `ReadS` parser from a `Grammar`. -}
genReadS :: Grammar a -> ReadS a
genReadS = runParsor

{- | Use a `Grammar` to parse a `String`. -}
readGrammar :: Grammar a -> String -> [a]
readGrammar grammar str =
  [ a
  | (a, remaining) <- genReadS grammar str
  , remaining == []
  ]

{- | Generate `ShowS` printers from a `Grammar`. -}
genShowS :: Alternative f => Grammar a -> a -> f ShowS
genShowS = runPrintor

{- | Use a `Grammar` to print `String`s. -}
showGrammar :: Alternative f => Grammar a -> a -> f String
showGrammar grammar a = ($ "") <$> genShowS grammar a

{- | Generate a `RegEx` from a `Grammar`.
This will infinite loop if your `Grammar` includes a `ruleRec`,
otherwise it will inline all rules and produce a regular expression.
-}
genRegEx :: Grammar a -> RegEx
genRegEx (DiRegEx rex) = rex

{- | Generate a context free grammar,
consisting of a @"start"@ and named `RegEx`es, from a `Grammar`.
-}
genGrammar :: Grammar a -> [(String, RegEx)]
genGrammar (DiGrammar (DiRegEx start) rules) =
  ("start", start) : toList rules

{- | Print a `Grammar`.-}
printGrammar :: Grammar a -> IO ()
printGrammar gram = for_ (genGrammar gram) $ \(name_i, rule_i) -> do
  putStr name_i
  putStr " = "
  putStrLn (regexString rule_i)

{- | The `RegEx` `String`.

>>> let rex = Alternate (Terminal "xy") (KleenePlus (Terminal "z"))
>>> putStrLn (regexString rex)
xy|z+
-}
regexString :: RegEx -> String
regexString rex = maybe "\\q" id (showGrammar regexGrammar rex)

{- | Parse a `RegEx` from a `String`.

>>> let str = "xy|z+"
>>> stringRegEx str
Alternate (Terminal "xy") (KleenePlus (Terminal "z"))

`Fail` if the `String` is not a valid regular expression.

>>> let bad = ")("
>>> stringRegEx bad
Fail
-}
stringRegEx :: String -> RegEx
stringRegEx str = case readGrammar regexGrammar str of
  [] -> Fail
  rex:_ -> normRegEx rex

-- RegEx Grammar --

{- | `regexGrammar` provides an important example of a `Grammar`.
Take a look at the source to see its definition.

>>> printGrammar regexGrammar
start = \q{regex}
alternate = \q{sequence}(\|\q{sequence})*
any = \.
atom = \q{nonterminal}|\q{fail}|\q{class-in}|\q{class-not-in}|\q{category-in}|\q{category-not-in}|\q{char}|\q{any}|\q{parenthesized}
category = Ll|Lu|Lt|Lm|Lo|Mn|Mc|Me|Nd|Nl|No|Pc|Pd|Ps|Pe|Pi|Pf|Po|Sm|Sc|Sk|So|Zs|Zl|Zp|Cc|Cf|Cs|Co|Cn
category-in = \\p\{\q{category}\}
category-not-in = \\P\{\q{category}\}
char = \q{char-literal}|\q{char-escaped}
char-escaped = \\[\$\(\)\*\+\.\?\[\\\]\^\{\|\}]
char-literal = [^\$\(\)\*\+\.\?\[\\\]\^\{\|\}]
class-in = \[\q{char}*\]
class-not-in = \[\^\q{char}*\]
expression = \q{terminal}|\q{kleene-optional}|\q{kleene-star}|\q{kleene-plus}|\q{atom}
fail = \\q
kleene-optional = \q{atom}\?
kleene-plus = \q{atom}\+
kleene-star = \q{atom}\*
nonterminal = \\q\{\q{char}*\}
parenthesized = \(\q{regex}\)
regex = \q{alternate}
sequence = \q{expression}*
terminal = \q{char}+

-}
regexGrammar :: Grammar RegEx
regexGrammar = ruleRec "regex" $ \rex -> altG rex

altG :: Grammarr RegEx RegEx
altG rex = rule "alternate" $
  chainl1 _Alternate (sepBy "|") (seqG rex)

anyG :: Grammar RegEx
anyG = rule "any" $ _AnyChar >?< "."

atomG :: Grammarr RegEx RegEx
atomG rex = rule "atom" $
  nonterminalG
  <|> failG
  <|> classInG
  <|> classNotInG
  <|> categoryInG
  <|> categoryNotInG
  <|> _Terminal >?< charG >:< pure ""
  <|> anyG
  <|> parenG rex

categoryG :: Grammar GeneralCategory
categoryG = rule "category" $
  _LowercaseLetter >?< "Ll"
  <|> _UppercaseLetter >?< "Lu"
  <|> _TitlecaseLetter >?< "Lt"
  <|> _ModifierLetter >?< "Lm"
  <|> _OtherLetter >?< "Lo"
  <|> _NonSpacingMark >?< "Mn"
  <|> _SpacingCombiningMark >?< "Mc"
  <|> _EnclosingMark >?< "Me"
  <|> _DecimalNumber >?< "Nd"
  <|> _LetterNumber >?< "Nl"
  <|> _OtherNumber >?< "No"
  <|> _ConnectorPunctuation >?< "Pc"
  <|> _DashPunctuation >?< "Pd"
  <|> _OpenPunctuation >?< "Ps"
  <|> _ClosePunctuation >?< "Pe"
  <|> _InitialQuote >?< "Pi"
  <|> _FinalQuote >?< "Pf"
  <|> _OtherPunctuation >?< "Po"
  <|> _MathSymbol >?< "Sm"
  <|> _CurrencySymbol >?< "Sc"
  <|> _ModifierSymbol >?< "Sk"
  <|> _OtherSymbol >?< "So"
  <|> _Space >?< "Zs"
  <|> _LineSeparator >?< "Zl"
  <|> _ParagraphSeparator >?< "Zp"
  <|> _Control >?< "Cc"
  <|> _Format >?< "Cf"
  <|> _Surrogate >?< "Cs"
  <|> _PrivateUse >?< "Co"
  <|> _NotAssigned >?< "Cn"

categoryInG :: Grammar RegEx
categoryInG = rule "category-in" $
  _InCategory >?< "\\p{" >* categoryG *< "}"

categoryNotInG :: Grammar RegEx
categoryNotInG = rule "category-not-in" $
  _NotInCategory >?< "\\P{" >* categoryG *< "}"

charG :: Grammar Char
charG = rule "char" $ charLiteralG <|> charEscapedG

charEscapedG :: Grammar Char
charEscapedG = rule "char-escaped" $ "\\" >* inClass charsReserved

charLiteralG :: Grammar Char
charLiteralG = rule "char-literal" $ notInClass charsReserved

charsReserved :: String
charsReserved = "$()*+.?[\\]^{|}"

classInG :: Grammar RegEx
classInG = rule "class-in" $
  _InClass >?< "[" >* manyP charG *< "]"

classNotInG :: Grammar RegEx
classNotInG = rule "class-not-in" $
  _NotInClass >?< "[^" >* manyP charG *< "]"

exprG :: Grammarr RegEx RegEx
exprG rex = rule "expression" $
  terminalG
  <|> kleeneOptG rex
  <|> kleeneStarG rex
  <|> kleenePlusG rex
  <|> atomG rex

failG :: Grammar RegEx
failG = rule "fail" $ _Fail >?< "\\q"

nonterminalG :: Grammar RegEx
nonterminalG = rule "nonterminal" $
  _NonTerminal >?< "\\q{" >* manyP charG *< "}"

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
  chainl _Sequence (_Terminal . _Empty) noSep (exprG rex)

terminalG :: Grammar RegEx
terminalG = rule "terminal" $
  _Terminal >?< someP charG
