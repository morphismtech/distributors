{- |
Module      : Control.Lens.Grammar
Description : grammar hierarchy
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable

See Chomsky, [On Certain Formal Properties of Grammars]
(https://somr.info/lib/Chomsky_1959.pdf)
-}

module Control.Lens.Grammar
  ( -- * Regular grammar
    RegGrammar
  , Lexical
  , RegString (..)
  , regstringG
  , regexGrammar
    -- * Context-free grammar
  , Grammar
  , RegBnf (..)
  , regbnfG
  , regbnfGrammar
    -- * Context-sensitive grammar
  , CtxGrammar
  , printG
  , parseG
  , unparseG
    -- * Utility
  , putStringLn
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.PartialIso
import Control.Lens.Grammar.BackusNaur
import Control.Lens.Grammar.Boole
import Control.Lens.Grammar.Kleene
import Control.Lens.Grammar.Token
import Control.Lens.Grammar.Symbol
import Data.Maybe hiding (mapMaybe)
import Data.Monoid
import Data.Profunctor.Distributor
import Data.Profunctor.Filtrator
import Data.Profunctor.Monadic
import Data.Profunctor.Monoidal
import Data.Profunctor.Grammar
import qualified Data.Set as Set
import Data.String
import GHC.Exts
import Prelude hiding (filter)
import Witherable

{- |
A regular grammar may be constructed using
`Lexical` and `Alternator` combinators.
Let's see an example using
[semantic versioning](https://semver.org/).

>>> import Numeric.Natural (Natural)
>>> import Control.Lens (Iso', iso)
>>> :{
data SemVer = SemVer          -- e.g., 2.1.5-rc.1+build.123
  { major         :: Natural  -- e.g., 1
  , minor         :: Natural  -- e.g., 2
  , patch         :: Natural  -- e.g., 3
  , preRelease    :: [String] -- e.g., "alpha.1", "rc.2"
  , buildMetadata :: [String] -- e.g., "build.123", "20130313144700"
  }
  deriving (Eq, Ord, Show, Read)
:}

We'd like to define an optic @_SemVer@,
corresponding to the constructor pattern @SemVer@.
Unfortunately, we can't use TemplateHaskell to generate it in [GHCi]
(https://wiki.haskell.org/GHC/GHCi),
which is used to test this documenation.
Normally we would write `makeNestedPrisms` @''SemVer@,
but here is equivalent explicit Haskell code instead.
Since @SemVer@ is a newtype, @_SemVer@ can be an `Control.Lens.Iso.Iso`.

>>> :set -XRecordWildCards
>>> :{
_SemVer :: Iso' SemVer (Natural, (Natural, (Natural, ([String], [String]))))
_SemVer = iso
  (\SemVer {..} -> (major, (minor, (patch, (preRelease, buildMetadata)))))
  (\(major, (minor, (patch, (preRelease, buildMetadata)))) -> SemVer {..})
:}

Now we can build a `RegGrammar` for @SemVer@ using the "idiom" style of
`Applicative` parsing with a couple modifications.

>>> :{
semverGrammar :: RegGrammar Char SemVer
semverGrammar = _SemVer
  >?  numberG
  >*< terminal "." >* numberG
  >*< terminal "." >* numberG
  >*< option [] (terminal "-" >* identifiersG)
  >*< option [] (terminal "+" >* identifiersG)
  where
    numberG = iso show read >~ someP (asIn @Char DecimalNumber)
    identifiersG = several1 (sepBy (terminal ".")) (someP charG)
    charG = asIn LowercaseLetter
      <|> asIn UppercaseLetter
      <|> asIn DecimalNumber
      <|> token '-'
:}

Instead of using the constructor @SemVer@ with the `Functor` applicator `<$>`,
we use the optic @_SemVer@ we defined and the `Choice` applicator `>?`;
although, we could have used the `Profunctor` applicator `>~` instead,
because @_SemVer@ is an `Control.Lens.Iso.Iso`. A few `Alternative`
combinators like `<|>` work both `Functor`ially and `Profunctor`ially.

+------------+---------------+
| Functorial | Profunctorial |
+============+===============+
| @SemVer@   | @_SemVer@     |
+------------+---------------+
| `<$>`      | `>?`          |
+------------+---------------+
| `*>`       | `>*`          |
+------------+---------------+
| `<*`       | `*<`          |
+------------+---------------+
| `<*>`      | `>*<`         |
+------------+---------------+
| `<|>`      | `<|>`         |
+------------+---------------+
| `option`   | `option`      |
+------------+---------------+
| `choice`   | `choice`      |
+------------+---------------+
| `many`     | `manyP`       |
+------------+---------------+
| `some`     | `someP`       |
+------------+---------------+
| `optional` | `optionalP`   |
+------------+---------------+

You can generate a `RegString` from a `RegGrammar` with `regstringG`.

>>> putStringLn (regstringG semverGrammar)
\p{Nd}+(.\p{Nd}+(.\p{Nd}+((-((\p{Ll}|\p{Lu}|\p{Nd}|-)+(.(\p{Ll}|\p{Lu}|\p{Nd}|-)+)*))?(\+((\p{Ll}|\p{Lu}|\p{Nd}|-)+(.(\p{Ll}|\p{Lu}|\p{Nd}|-)+)*))?)))

You can also generate parsers and printers.

>>> [parsed | (parsed, "") <- parseG semverGrammar "2.1.5-rc.1+build.123"]
[SemVer {major = 2, minor = 1, patch = 5, preRelease = ["rc","1"], buildMetadata = ["build","123"]}]

Parsing `uncons`es tokens left-to-right, from the beginning of a string.
Unparsing, on the other hand, `snoc`s tokens left-to-right, to the end of a string.

>>> unparseG semverGrammar (SemVer 1 0 0 ["alpha"] []) "SemVer: " :: Maybe String
Just "SemVer: 1.0.0-alpha"

Printing, on the gripping hand, `cons`es tokens right-to-left, to the beginning of a string.

>>> ($ " is the SemVer.") <$> printG semverGrammar (SemVer 1 2 3 [] []) :: Maybe String
Just "1.2.3 is the SemVer."

`Profunctor`ial combinators give us correct-by-construction invertible parsers.
New `RegGrammar` generators can be defined with new instances of `Lexical` `Alternator`s.
-}
type RegGrammar token a = forall p.
  ( Lexical token p
  , Alternator p
  ) => p a a

{- |
>>> import Numeric.Natural (Natural)
>>> import Control.Lens (Prism', prism')
>>> :{
data Arith
  = Num Natural
  | Add Arith Arith
  | Mul Arith Arith
  deriving stock (Eq, Ord, Show, Read)
:}

>>> :{
_Num :: Prism' Arith Natural
_Num = prism' Num (\case Num n -> Just n; _ -> Nothing)
_Add, _Mul :: Prism' Arith (Arith, Arith)
_Add = prism' (uncurry Add) (\case Add x y -> Just (x,y); _ -> Nothing)
_Mul = prism' (uncurry Mul) (\case Mul x y -> Just (x,y); _ -> Nothing)
:}

>>> :{
arithGrammar :: Grammar Char Arith
arithGrammar = ruleRec "arith" sumG
  where
    sumG arith = rule "sum" $
      chain1 Left _Add (sepBy (terminal "+")) (prodG arith)
    prodG arith = rule "product" $
      chain1 Left _Mul (sepBy (terminal "*")) (factorG arith)
    factorG arith = rule "factor" $
      numberG <|> terminal "(" >* arith *< terminal ")"
    numberG = rule "number" $
      _Num . iso show read >? someP (asIn @Char DecimalNumber)
:}

>>> [x | (x,"") <- parseG arithGrammar "1+2*3+4"]
[Add (Add (Num 1) (Mul (Num 2) (Num 3))) (Num 4)]

>>> unparseG arithGrammar (Add (Num 1) (Mul (Num 2) (Num 3))) "" :: Maybe String
Just "1+2*3"

>>> do pr <- printG arithGrammar (Num 69); return (pr "") :: Maybe String
Just "69"

>>> putStringLn (regbnfG arithGrammar)
{start} = \q{arith}
{arith} = \q{sum}
{factor} = \q{number}|\(\q{arith}\)
{number} = \p{Nd}+
{product} = \q{factor}(\*\q{factor})*
{sum} = \q{product}(\+\q{product})*
-}
type Grammar token a = forall p.
  ( Lexical token p
  , forall x. BackusNaurForm (p x x)
  , Alternator p
  ) => p a a

type CtxGrammar token a = forall p.
  ( Lexical token p
  , forall x. BackusNaurForm (p x x)
  , Alternator p
  , Monadic p
  , Filtrator p
  ) => p a a

{- |
`Lexical` combinators include

* `terminal` symbols from "Control.Lens.Grammar.Symbol";
* `Tokenized` combinators from "Control.Lens.Grammar.Token";
* `tokenClass` `BooleanAlgebra` combinators from "Control.Lens.Grammar.Boole".
-}
type Lexical token p =
  ( forall x y. (x ~ (), y ~ ()) => TerminalSymbol token (p x y)
  , forall x y. (x ~ token, y ~ token) => TokenAlgebra token (p x y)
  ) :: Constraint

newtype RegString = RegString {runRegString :: RegEx Char}
  deriving newtype
    ( Eq, Ord
    , Semigroup, Monoid, KleeneStarAlgebra
    , Tokenized Char, TokenAlgebra Char
    , TerminalSymbol Char, NonTerminalSymbol
    , Matching String
    )

newtype RegBnf = RegBnf {runRegBnf :: Bnf RegString}
  deriving newtype
    ( Eq, Ord
    , Semigroup, Monoid, KleeneStarAlgebra
    , Tokenized Char, TokenAlgebra Char
    , TerminalSymbol Char, NonTerminalSymbol
    , BackusNaurForm
    )
instance Matching String RegBnf where
  word =~ pattern = word =~ liftBnf1 runRegString (runRegBnf pattern)

makeNestedPrisms ''Bnf
makeNestedPrisms ''RegEx
makeNestedPrisms ''RegExam
makeNestedPrisms ''CategoryTest
makeNestedPrisms ''GeneralCategory
makeNestedPrisms ''RegString
makeNestedPrisms ''RegBnf

{- |
>>> putStringLn (regbnfG regexGrammar)
{start} = \q{regex}
{alternate} = \q{sequence}(\|\q{sequence})*
{atom} = (\\q\{)\q{char}*\}|\q{char}|\q{char-class}|\(\q{regex}\)
{category} = Ll|Lu|Lt|Lm|Lo|Mn|Mc|Me|Nd|Nl|No|Pc|Pd|Ps|Pe|Pi|Pf|Po|Sm|Sc|Sk|So|Zs|Zl|Zp|Cc|Cf|Cs|Co|Cn
{category-test} = (\\p\{)\q{category}\}|(\\P\{)(\q{category}(\|\q{category})*)\}
{char} = [^\(\)\*\+\?\[\\\]\^\{\|\}\P{Cc}]|\\\q{char-escaped}
{char-any} = \[\^\]
{char-class} = \q{fail}|\q{char-any}|\q{one-of}|\q{not-one-of}|\q{category-test}
{char-control} = NUL|SOH|STX|ETX|EOT|ENQ|ACK|BEL|BS|HT|LF|VT|FF|CR|SO|SI|DLE|DC1|DC2|DC3|DC4|NAK|SYN|ETB|CAN|EM|SUB|ESC|FS|GS|RS|US|DEL|PAD|HOP|BPH|NBH|IND|NEL|SSA|ESA|HTS|HTJ|VTS|PLD|PLU|RI|SS2|SS3|DCS|PU1|PU2|STS|CCH|MW|SPA|EPA|SOS|SGCI|SCI|CSI|ST|OSC|PM|APC
{char-escaped} = [\(\)\*\+\?\[\\\]\^\{\|\}]|\q{char-control}
{expression} = \q{atom}\?|\q{atom}\*|\q{atom}\+|\q{atom}
{fail} = \[\]
{not-one-of} = (\[\^)\q{char}+(\q{category-test}?\])
{one-of} = \[\q{char}+\]
{regex} = \q{alternate}
{sequence} = \q{char}*|\q{expression}*
-}
regexGrammar :: Grammar Char RegString
regexGrammar = _RegString >~ ruleRec "regex" altG
  where
    altG rex = rule "alternate" $
      chain1 Left (_RegExam . _Alternate) (sepBy (terminal "|")) (seqG rex)

    seqG rex = rule "sequence" $ choice
      [ _Terminal >? manyP charG
      , chain Left _Sequence (_Terminal . _Empty) noSep (exprG rex)
      ]

    exprG rex = rule "expression" $ choice
      [ _KleeneOpt >? atomG rex *< terminal "?"
      , _KleeneStar >? atomG rex *< terminal "*"
      , _KleenePlus >? atomG rex *< terminal "+"
      , atomG rex
      ]

    atomG rex = rule "atom" $ choice
      [ _NonTerminal >? terminal "\\q{" >* manyP charG *< terminal "}"
      , _Terminal >? charG >:< asEmpty
      , _RegExam >? classG
      , terminal "(" >* rex *< terminal ")"
      ]

    catTestG = rule "category-test" $ choice
      [ _AsIn >? terminal "\\p{" >* categoryG *< terminal "}"
      , _NotAsIn >? several1 (sepBy (terminal "|"))
          { beginBy = terminal "\\P{"
          , endBy = terminal "}"
          } categoryG
      ]

    categoryG = rule "category" $ choice
      [ _LowercaseLetter >? terminal "Ll"
      , _UppercaseLetter >? terminal "Lu"
      , _TitlecaseLetter >? terminal "Lt"
      , _ModifierLetter >? terminal "Lm"
      , _OtherLetter >? terminal "Lo"
      , _NonSpacingMark >? terminal "Mn"
      , _SpacingCombiningMark >? terminal "Mc"
      , _EnclosingMark >? terminal "Me"
      , _DecimalNumber >? terminal "Nd"
      , _LetterNumber >? terminal "Nl"
      , _OtherNumber >? terminal "No"
      , _ConnectorPunctuation >? terminal "Pc"
      , _DashPunctuation >? terminal "Pd"
      , _OpenPunctuation >? terminal "Ps"
      , _ClosePunctuation >? terminal "Pe"
      , _InitialQuote >? terminal "Pi"
      , _FinalQuote >? terminal "Pf"
      , _OtherPunctuation >? terminal "Po"
      , _MathSymbol >? terminal "Sm"
      , _CurrencySymbol >? terminal "Sc"
      , _ModifierSymbol >? terminal "Sk"
      , _OtherSymbol >? terminal "So"
      , _Space >? terminal "Zs"
      , _LineSeparator >? terminal "Zl"
      , _ParagraphSeparator >? terminal "Zp"
      , _Control >? terminal "Cc"
      , _Format >? terminal "Cf"
      , _Surrogate >? terminal "Cs"
      , _PrivateUse >? terminal "Co"
      , _NotAssigned >? terminal "Cn"
      ]

    classG = rule "char-class" $ choice
      [ _Fail >? failG
      , _Pass >? anyG
      , _OneOf >? oneOfG
      , _NotOneOf >? notOneOfG
      , _NotOneOf >? pure Set.empty >*< catTestG
      ]

    failG = rule "fail" $ terminal "[]"

    anyG = rule "char-any" $ terminal "[^]"

    oneOfG = rule "one-of" $ terminal "[" >* several1 noSep charG *< terminal "]"

    notOneOfG = rule "not-one-of" $
      terminal "[^" >* several1 noSep charG
        >*< option (NotAsIn Set.empty) catTestG
        *< terminal "]"

charG :: Grammar Char Char
charG = rule "char" $
  tokenClass (notOneOf charsReserved >&&< notAsIn Control)
  <|> terminal "\\" >* charEscapedG
  where
    charEscapedG = rule "char-escaped" $
      oneOf charsReserved <|> charControlG

    charsReserved = "()*+?[\\]^{|}"

    charControlG = rule "char-control" $ choice
      [ only '\NUL' >? terminal "NUL"
      , only '\SOH' >? terminal "SOH"
      , only '\STX' >? terminal "STX"
      , only '\ETX' >? terminal "ETX"
      , only '\EOT' >? terminal "EOT"
      , only '\ENQ' >? terminal "ENQ"
      , only '\ACK' >? terminal "ACK"
      , only '\BEL' >? terminal "BEL"
      , only '\BS' >? terminal "BS"
      , only '\HT' >? terminal "HT"
      , only '\LF' >? terminal "LF"
      , only '\VT' >? terminal "VT"
      , only '\FF' >? terminal "FF"
      , only '\CR' >? terminal "CR"
      , only '\SO' >? terminal "SO"
      , only '\SI' >? terminal "SI"
      , only '\DLE' >? terminal "DLE"
      , only '\DC1' >? terminal "DC1"
      , only '\DC2' >? terminal "DC2"
      , only '\DC3' >? terminal "DC3"
      , only '\DC4' >? terminal "DC4"
      , only '\NAK' >? terminal "NAK"
      , only '\SYN' >? terminal "SYN"
      , only '\ETB' >? terminal "ETB"
      , only '\CAN' >? terminal "CAN"
      , only '\EM' >? terminal "EM"
      , only '\SUB' >? terminal "SUB"
      , only '\ESC' >? terminal "ESC"
      , only '\FS' >? terminal "FS"
      , only '\GS' >? terminal "GS"
      , only '\RS' >? terminal "RS"
      , only '\US' >? terminal "US"
      , only '\DEL' >? terminal "DEL"
      , only '\x80' >? terminal "PAD"
      , only '\x81' >? terminal "HOP"
      , only '\x82' >? terminal "BPH"
      , only '\x83' >? terminal "NBH"
      , only '\x84' >? terminal "IND"
      , only '\x85' >? terminal "NEL"
      , only '\x86' >? terminal "SSA"
      , only '\x87' >? terminal "ESA"
      , only '\x88' >? terminal "HTS"
      , only '\x89' >? terminal "HTJ"
      , only '\x8A' >? terminal "VTS"
      , only '\x8B' >? terminal "PLD"
      , only '\x8C' >? terminal "PLU"
      , only '\x8D' >? terminal "RI"
      , only '\x8E' >? terminal "SS2"
      , only '\x8F' >? terminal "SS3"
      , only '\x90' >? terminal "DCS"
      , only '\x91' >? terminal "PU1"
      , only '\x92' >? terminal "PU2"
      , only '\x93' >? terminal "STS"
      , only '\x94' >? terminal "CCH"
      , only '\x95' >? terminal "MW"
      , only '\x96' >? terminal "SPA"
      , only '\x97' >? terminal "EPA"
      , only '\x98' >? terminal "SOS"
      , only '\x99' >? terminal "SGCI"
      , only '\x9A' >? terminal "SCI"
      , only '\x9B' >? terminal "CSI"
      , only '\x9C' >? terminal "ST"
      , only '\x9D' >? terminal "OSC"
      , only '\x9E' >? terminal "PM"
      , only '\x9F' >? terminal "APC"
      ]

{- |
>>> putStringLn (regbnfG regbnfGrammar)
{start} = \q{regbnf}
{alternate} = \q{sequence}(\|\q{sequence})*
{atom} = (\\q\{)\q{char}*\}|\q{char}|\q{char-class}|\(\q{regex}\)
{category} = Ll|Lu|Lt|Lm|Lo|Mn|Mc|Me|Nd|Nl|No|Pc|Pd|Ps|Pe|Pi|Pf|Po|Sm|Sc|Sk|So|Zs|Zl|Zp|Cc|Cf|Cs|Co|Cn
{category-test} = (\\p\{)\q{category}\}|(\\P\{)(\q{category}(\|\q{category})*)\}
{char} = [^\(\)\*\+\?\[\\\]\^\{\|\}\P{Cc}]|\\\q{char-escaped}
{char-any} = \[\^\]
{char-class} = \q{fail}|\q{char-any}|\q{one-of}|\q{not-one-of}|\q{category-test}
{char-control} = NUL|SOH|STX|ETX|EOT|ENQ|ACK|BEL|BS|HT|LF|VT|FF|CR|SO|SI|DLE|DC1|DC2|DC3|DC4|NAK|SYN|ETB|CAN|EM|SUB|ESC|FS|GS|RS|US|DEL|PAD|HOP|BPH|NBH|IND|NEL|SSA|ESA|HTS|HTJ|VTS|PLD|PLU|RI|SS2|SS3|DCS|PU1|PU2|STS|CCH|MW|SPA|EPA|SOS|SGCI|SCI|CSI|ST|OSC|PM|APC
{char-escaped} = [\(\)\*\+\?\[\\\]\^\{\|\}]|\q{char-control}
{expression} = \q{atom}\?|\q{atom}\*|\q{atom}\+|\q{atom}
{fail} = \[\]
{not-one-of} = (\[\^)\q{char}+(\q{category-test}?\])
{one-of} = \[\q{char}+\]
{regbnf} = (\{start\} = )\q{regex}(\LF\q{rule})*
{regex} = \q{alternate}
{rule} = \{\q{char}*(\} = )\q{regex}
{sequence} = \q{char}*|\q{expression}*
-}
regbnfGrammar :: Grammar Char RegBnf
regbnfGrammar = rule "regbnf" $ _RegBnf . _Bnf >~
  terminal "{start} = " >* regexGrammar
    >*< several noSep (terminal "\n" >* ruleG)
  where
    ruleG = rule "rule" $ terminal "{" >* manyP charG *< terminal "} = "
      >*< regexGrammar

regstringG :: RegGrammar Char a -> RegString
regstringG rex = runGrammor rex

regbnfG :: Grammar Char a -> RegBnf
regbnfG bnf = runGrammor bnf

printG
  :: ( Cons string string token token
     , IsList string
     , Item string ~ token
     , Categorized token
     , Alternative m
     , Monad m
     , Filterable m
     )
  => CtxGrammar token a -> a -> m (string -> string)
printG printor = printP printor

parseG
  :: ( Cons string string token token
     , Snoc string string token token
     , IsList string
     , Item string ~ token
     , Categorized token
     , Alternative m
     , Monad m
     , Filterable m
     )
  => CtxGrammar token a -> string -> m (a, string)
parseG parsor = parseP parsor

unparseG
  :: ( Cons string string token token
     , Snoc string string token token
     , IsList string
     , Item string ~ token
     , Categorized token
     , Alternative m
     , Monad m
     , Filterable m
     )
  => CtxGrammar token a -> a -> string -> m string
unparseG parsor = unparseP parsor

putStringLn :: (IsList string, Item string ~ Char) => string -> IO ()
putStringLn = putStrLn . toList

instance IsList RegString where
  type Item RegString = Char
  fromList
    = fromMaybe zeroK
    . listToMaybe
    . mapMaybe prsF
    . parseP regexGrammar
    where
      prsF (rex,"") = Just rex
      prsF _ = Nothing
  toList
    = maybe "[]" ($ "")
    . printP regexGrammar
instance IsString RegString where
  fromString = fromList
instance Show RegString where
  showsPrec precision = showsPrec precision . toList
instance Read RegString where
  readsPrec _ str = [(fromList str, "")]
instance IsList RegBnf where
  type Item RegBnf = Char
  fromList
    = fromMaybe zeroK
    . listToMaybe
    . mapMaybe prsF
    . parseP regbnfGrammar
    where
      prsF (regbnf,"") = Just regbnf
      prsF _ = Nothing
  toList
    = maybe "{start} = []" ($ "")
    . printP regbnfGrammar
instance IsString RegBnf where
  fromString = fromList
instance Show RegBnf where
  showsPrec precision = showsPrec precision . toList
instance Read RegBnf where
  readsPrec _ str = [(fromList str, "")]
