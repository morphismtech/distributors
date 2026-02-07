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
Since @SemVer@ has only one constructor,
@_SemVer@ can be an `Control.Lens.Iso.Iso`.

>>> :set -XRecordWildCards
>>> import Control.Lens (Iso', iso)
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

{- | Context-free `Grammar`s add two capabilities to `RegGrammar`s,
coming from the `BackusNaurForm` interface

* `rule` abstraction,
* and general recursion.

`regexGrammar` and `regbnfGrammar` are examples of context-free
`Grammar`s. Regular expressions are a form of expression algebra.
Let's see a similar but simpler example,
the algebra of arithmetic expressions of natural numbers.

>>> import Numeric.Natural (Natural)
>>> :{
data Arith
  = Num Natural
  | Add Arith Arith
  | Mul Arith Arith
  deriving stock (Eq, Ord, Show, Read)
:}

Here are `Control.Lens.Prism.Prism`s for the constructor patterns.

>>> import Control.Lens (Prism', prism')
>>> :{
_Num :: Prism' Arith Natural
_Num = prism' Num (\case Num n -> Just n; _ -> Nothing)
_Add, _Mul :: Prism' Arith (Arith, Arith)
_Add = prism' (uncurry Add) (\case Add x y -> Just (x,y); _ -> Nothing)
_Mul = prism' (uncurry Mul) (\case Mul x y -> Just (x,y); _ -> Nothing)
:}

Now we can build a `Grammar` for @Arith@
by combining "idiom" style with named `rule`s,
and tying the recursive loop
(caused by parenthesization)
with `ruleRec`.

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

We can generate a `RegBnf`, printers and parsers from @arithGrammar@.

>>> putStringLn (regbnfG arithGrammar)
{start} = \q{arith}
{arith} = \q{sum}
{factor} = \q{number}|\(\q{arith}\)
{number} = \p{Nd}+
{product} = \q{factor}(\*\q{factor})*
{sum} = \q{product}(\+\q{product})*

>>> [x | (x,"") <- parseG arithGrammar "1+2*3+4"]
[Add (Add (Num 1) (Mul (Num 2) (Num 3))) (Num 4)]
>>> unparseG arithGrammar (Add (Num 1) (Mul (Num 2) (Num 3))) "" :: Maybe String
Just "1+2*3"
>>> do pr <- printG arithGrammar (Num 69); return (pr "") :: Maybe String
Just "69"

-}
type Grammar token a = forall p.
  ( Lexical token p
  , forall x. BackusNaurForm (p x x)
  , Alternator p
  ) => p a a

{- |
In addition to context-sensitivity via `Monadic` combinators,
`CtxGrammar`s adds general filtration via `Filtrator` to `Grammar`s.

>>> :{
palindromeG :: CtxGrammar Char String
palindromeG = rule "palindrome" $
  satisfied (\wrd -> reverse wrd == wrd) >?< manyP (anyToken @Char)
:}

The `satisfied` pattern is used together with the `Choice` &
`Data.Profunctor.Cochoice` applicator `>?<` for general filtration.
For context-sensitivity,
the `Monadic` interface is used by importing "Data.Profunctor.Monadic"
qualified and using a "bonding" notation which mixes
"idiom" style with qualified do-notation.
Let's use length-encoded vectors of numbers as an example.

>>> import Numeric.Natural (Natural)
>>> import Control.Lens.Iso (Iso', iso)
>>> :set -XRecordWildCards
>>> :{
data LenVec = LenVec {length :: Natural, vector :: [Natural]}
  deriving (Eq, Ord, Show, Read)
_LenVec :: Iso' LenVec (Natural, [Natural])
_LenVec = iso (\LenVec {..} -> (length, vector)) (\(length, vector) -> LenVec {..})
:}

>>> :set -XQualifiedDo
>>> import qualified Data.Profunctor.Monadic as P
>>> :{
lenvecGrammar :: CtxGrammar Char LenVec
lenvecGrammar = _LenVec >? P.do
  let
    numberG = iso show read >~ someP (asIn @Char DecimalNumber)
    vectorG n = intercalateP n (sepBy (terminal ",")) numberG
  len <- numberG             -- bonds to _LenVec
  terminal ";"               -- doesn't bond
  vectorG (fromIntegral len) -- bonds to _LenVec
:}

The qualified do-notation changes the signature of
@P.@`Data.Profunctor.Monadic.>>=`,
so that we must apply the constructor pattern @_LenVec@
to the do-block with the `>?` applicator.
Any bound named variable, @var <- action@,
gets "bonded" to the constructor pattern.
Any unbound actions, except for the last action in the do-block,
does not get bonded to the pattern.
The last action does get bonded to the pattern.
Any unnamed bound action, @_ <- action@,
also gets bonded to the pattern,
but being unnamed means it isn't added to the context.
If all bound actions are unnamed, then a `CtxGrammar` can
be rewritten as a `Grammar` since it is context-free.
We can't generate a `RegBnf` since the `rule`s
of a `CtxGrammar` aren't static, but dynamic and contextual.
We can generate parsers and printers as expected.

>>> [vec | (vec, "") <- parseG lenvecGrammar "3;1,2,3"] :: [LenVec]
[LenVec {length = 3, vector = [1,2,3]}]
>>> [vec | (vec, "") <- parseG lenvecGrammar "0;1,2,3"] :: [LenVec]
[]
>>> [pr "" | pr <- printG lenvecGrammar (LenVec 2 [6,7])] :: [String]
["2;6,7"]
>>> [pr "" | pr <- printG lenvecGrammar (LenVec 200 [100])] :: [String]
[]
>>> [pal | word <- ["racecar", "word"], (pal, "") <- parseG palindromeG word]
["racecar"]
-}
type CtxGrammar token a = forall p.
  ( Lexical token p
  , forall x. BackusNaurForm (p x x)
  , Alternator p
  , Filtrator p
  , Monadic p
  ) => p a a

{- |
`Lexical` combinators include

* `terminal` symbols from "Control.Lens.Grammar.Symbol";
* `Tokenized` combinators from "Control.Lens.Grammar.Token";
* `tokenClass`es from "Control.Lens.Grammar.Boole".
-}
type Lexical token p =
  ( forall x y. (x ~ (), y ~ ()) => TerminalSymbol token (p x y)
  , forall x y. (x ~ token, y ~ token) => TokenAlgebra token (p x y)
  ) :: Constraint

{- | `RegString`s are an embedded domain specific language
of regular expression strings. Since they are strings,
they have a string-like interface.

>>> let rex = fromString "ab|c" :: RegString
>>> putStringLn rex
ab|c
>>> rex
"ab|c"

`RegString`s can be generated from `RegGrammar`s with `regstringG`.

>>> regstringG (terminal "a" >* terminal "b" <|> terminal "c")
"ab|c"

`RegString`s are actually stored as an algebraic datatype, `RegEx`.

>>> runRegString rex
RegExam (Alternate (Terminal "ab") (Terminal "c"))

`RegString`s are similar to regular expression strings in many other
programming languages. We can use them to see if a word and pattern
are `Matching`.

>>> "ab" =~ rex
True
>>> "c" =~ rex
True
>>> "xyz" =~ rex
False

Like `RegGrammar`s, `RegString`s can use all the `Lexical` combinators.
Unlike `RegGrammar`s, instead of using `Monoidal` and `Alternator` combinators,
`RegString`s use `Monoid` and `KleeneStarAlgebra` combinators.

>>> terminal "a" <> terminal "b" >|< terminal "c" :: RegString
"ab|c"
>>> mempty :: RegString
""

Since `RegString`s are a `KleeneStarAlgebra`,
they support Kleene quantifiers.

>>> starK rex
"(ab|c)*"
>>> plusK rex
"(ab|c)+"
>>> optK rex
"(ab|c)?"

Like other regular expression languages, `RegString`s support
character classes.

>>> oneOf "abc" :: RegString
"[abc]"
>>> notOneOf "abc" :: RegString
"[^abc]"

The character classes are used for failure, matching no character or string,
as well as the wildcard, matching any single character.

>>> zeroK :: RegString
"[]"
>>> anyToken :: RegString
"[^]"

Additional forms of character classes test for a character's `GeneralCategory`.

>>> asIn LowercaseLetter :: RegString
"\\p{Ll}"
>>> notAsIn Control :: RegString
"\\P{Cc}"

`KleeneStarAlgebra`s support alternation `>|<`,
and the `Tokenized` combinators are all negatable.
However, we'd like to be able to take the
intersection of character classes as well.
`RegString`s can combine characters' `tokenClass`es
using `BooleanAlgebra` combinators.

>>> tokenClass (notOneOf "abc" >&&< notOneOf "xyz") :: RegString
"[^abcxyz]"
>>> tokenClass (oneOf "abcxyz" >&&< notOneOf "xyz") :: RegString
"[abc]"
>>> tokenClass (notOneOf "#$%" >&&< notAsIn Control) :: RegString
"[^#$%\\P{Cc}]"
>>> tokenClass (allB notAsIn [MathSymbol, Control]) :: RegString
"\\P{Sm|Cc}"
>>> tokenClass (notB (oneOf "xyz")) :: RegString
"[^xyz]"

Ill-formed `RegString`s normalize to failure.

>>> fromString ")(" :: RegString
"[]"
-}
newtype RegString = RegString {runRegString :: RegEx Char}
  deriving newtype
    ( Eq, Ord
    , Semigroup, Monoid, KleeneStarAlgebra
    , Tokenized Char, TokenAlgebra Char
    , TerminalSymbol Char, NonTerminalSymbol
    , Matching String
    )

{- | `RegBnf`s are an embedded domain specific language
of Backus-Naur forms extended by regular expression strings.
Like `RegString`s they have a string-like interface.

>>> let bnf = fromString "{start} = foo|bar" :: RegBnf
>>> putStringLn bnf
{start} = foo|bar
>>> bnf
"{start} = foo|bar"

`RegBnf`s can be generated from context-free `Grammar`s with `regbnfG`.

>>> :type regbnfG regbnfGrammar
regbnfG regbnfGrammar :: RegBnf

Like `RegString`s, `RegBnf`s can be constructed using
`Lexical`, `Monoid` and `KleeneStarAlgebra` combinators.
But they also support `BackusNaurForm` `rule`s and `ruleRec`s.
-}
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

{- | `regexGrammar` is a context-free `Grammar` for `RegString`s.
It can't be a `RegGrammar`, since `RegString`s include parenthesization.
But [balanced parentheses](https://en.wikipedia.org/wiki/Dyck_language)
are a context-free language.

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
`regbnfGrammar` is a context-free `Grammar` for `RegBnf`s.
That means that it can generate a self-hosted definition.

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

{- | `regstringG` generates a `RegString` from a regular grammar.
Since context-free `Grammar`s and `CtxGrammar`s aren't necessarily regular,
the type system will prevent `regstringG` from being applied to them.
-}
regstringG :: RegGrammar Char a -> RegString
regstringG rex = runGrammor rex

{- | `regbnfG` generates a `RegBnf` from a context-free `Grammar`.
Since `CtxGrammar`s aren't context-free,
the type system will prevent `regbnfG` from being applied to a `CtxGrammar`.
It can apply to a `RegGrammar`.
-}
regbnfG :: Grammar Char a -> RegBnf
regbnfG bnf = runGrammor bnf

{- | `printG` generates a printer from a `CtxGrammar`.
Since both `RegGrammar`s and context-free `Grammar`s are `CtxGrammar`s,
the type system will allow `printG` to be applied to them.
Running the printer on a syntax value returns a function
that `cons`es tokens at the beginning of an input string,
from right to left.
-}
printG
  :: Cons string string token token
  => (IsList string, Item string ~ token, Categorized token)
  => (Alternative m, Monad m, Filterable m)
  => CtxGrammar token a
  -> a {- ^ syntax -}
  -> m (string -> string)
printG printor = printP printor

{- | `parseG` generates a parser from a `CtxGrammar`.
Since both `RegGrammar`s and context-free `Grammar`s are `CtxGrammar`s,
the type system will allow `parseG` to be applied to them.
Running the parser on an input string value `uncons`es
tokens from the beginning of an input string from left to right,
returning a syntax value and the remaining output string.
-}
parseG
  :: (Cons string string token token, Snoc string string token token)
  => (IsList string, Item string ~ token, Categorized token)
  => (Alternative m, Monad m, Filterable m)
  => CtxGrammar token a
  -> string {- ^ input -}
  -> m (a, string)
parseG parsor = parseP parsor

{- | `unparseG` generates an unparser from a `CtxGrammar`.
Since both `RegGrammar`s and context-free `Grammar`s are `CtxGrammar`s,
the type system will allow `unparseG` to be applied to them.
Running the unparser on a syntax value and an input string
`snoc`s tokens at the end of the string, from left to right,
returning the output string.
-}
unparseG
  :: (Cons string string token token, Snoc string string token token)
  => (IsList string, Item string ~ token, Categorized token)
  => (Alternative m, Monad m, Filterable m)
  => CtxGrammar token a
  -> a {- ^ syntax -}
  -> string {- ^ input -}
  -> m string
unparseG parsor = unparseP parsor

{- | `putStringLn` is a utility that generalizes `putStrLn`
to string-like interfaces such as `RegString` and `RegBnf`.
-}
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
