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
  , applicativeG
  , transducerG
    -- * Context-sensitive grammar
  , CtxGrammar
  , printG
  , parseG
  , unparseG
  , parsecG
  , unparsecG
  , readG
  , monadG
    -- * Haskell syntax grammars
  , naturalGrammar
  , NaturalSyntax (..)
  , DecimalDigit (..)
  , OctalDigit (..)
  , HexDigit (..)
  , _NaturalSyntax
  , naturalOctal
  , naturalHexadecimal
  , integerGrammar
  , Sign (..)
  , IntegerSyntax (..)
  , _IntegerSyntax
  , doubleGrammar
  , floatGrammar
  , FloatingSyntax (..)
  , _FloatingSyntax
    -- * Utility
  , putStringLn
    -- * Re-exports
  , module X
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.PartialIso
import Control.Lens.Grammar.BackusNaur
import Control.Lens.Grammar.Boole
import Control.Lens.Grammar.Kleene
import Control.Lens.Grammar.Machine
import Control.Lens.Grammar.Token
import Control.Lens.Grammar.Symbol
import Data.Bifunctor.Joker
import Data.List (foldl')
import Data.Maybe hiding (mapMaybe)
import Data.Monoid
import Data.Profunctor.Distributor
import Data.Profunctor.Filtrator
import Data.Profunctor.Monadic
import Data.Profunctor.Monoidal
import Data.Profunctor.Grammar
import Data.Profunctor.Grammar.Parsector
import Data.Profunctor.Separator
import Data.Ratio ((%))
import Data.String
import GHC.Exts
import Numeric (floatToDigits)
import Numeric.Natural
import Prelude hiding (filter)
import Text.ParserCombinators.ReadP (ReadP, readP_to_S)
import Witherable

-- Re-exports
import Control.Lens.Grammar.BackusNaur as X
import Control.Lens.Grammar.Boole as X
import Control.Lens.Grammar.Kleene as X
import Control.Lens.Grammar.Machine as X
import Control.Lens.Grammar.Symbol as X
import Control.Lens.Grammar.Token as X
import Control.Lens.PartialIso as X
import Control.Monad.Fail.Try as X
import Data.Profunctor.Distributor as X
import Data.Profunctor.Filtrator as X
import Data.Profunctor.Grammar as X
import Data.Profunctor.Grammar.Parsector as X
import Data.Profunctor.Monoidal as X
import Data.Profunctor.Separator as X
import Data.Traversable.Homogeneous as X

{- |
A regular grammar may be constructed using
`Lexical` and `Alternator` combinators.
Let's see an example using
[semantic versioning](https://semver.org/) syntax.

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
You could generate it with the TemplateHaskell combinator,
`makeNestedPrisms`.

@makeNestedPrisms ''SemVer@

Unfortunately, we can't use TemplateHaskell to generate it in [GHCi]
(https://wiki.haskell.org/GHC/GHCi),
which is used to test this documenation.
Here is equivalent Haskell code instead.
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
  >*< optionP _Empty (terminal "-" >* identifiersG)
  >*< optionP _Empty (terminal "+" >* identifiersG)
  where
    numberG = iso show read >~ someP (asIn @Char DecimalNumber)
    identifiersG = several1 (sepWith ".") (someP charG)
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
| `pure`     | `pureP`       |
+------------+---------------+
| `*>`       | `>*`          |
+------------+---------------+
| `<*`       | `*<`          |
+------------+---------------+
| `<*>`      | `>*<`         |
+------------+---------------+
| `empty`    | `empty`       |
+------------+---------------+
| `<|>`      | `<|>`         |
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
      chain1 Left _Add (sepWith "+") (prodG arith)
    prodG arith = rule "product" $
      chain1 Left _Mul (sepWith "*") (factorG arith)
    factorG arith = rule "factor" $
      numberG <|> terminal "(" >* arith *< terminal ")"
    numberG = rule "number" $
      _Num . iso show read >? someP (asIn @Char DecimalNumber)
:}

We can generate grammar strings, printers and parsers from @arithGrammar@.

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
>>> do pr <- printG arithGrammar (Num 69); pure (pr "") :: Maybe String
Just "69"

If all `rule`s are non-recursive, then a `Grammar`
can be rewritten as a `RegGrammar`.
Since Haskell permits general recursion, and `RegGrammar`s are
embedded in Haskell, you can define context-free grammars with them.
But it's recommended to use `Grammar`s for `rule` abstraction
and generator support for `ruleRec`.

-}
type Grammar token a = forall p.
  ( Lexical token p
  , Alternator p
  , forall x. BackusNaurForm (p x x)
  ) => p a a

{- | For context-sensitivity,
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
    vectorG n = intercalateP n (sepWith ",") numberG
  len <- numberG             -- bonds to _LenVec
  terminal ";"               -- doesn't bond
  vectorG (fromIntegral len) -- bonds to _LenVec
:}

The qualified do-notation changes the signature of
@P.@`Data.Profunctor.Monadic.>>=`,
so that we must apply the constructor pattern @_LenVec@
to the do-block with the `>?` applicator.
Any scoped bound action, @var <- action@,
gets "bonded" to the constructor pattern.
Any unbound actions, except for the last action in the do-block,
does not get bonded to the pattern.
The last action does get bonded to the pattern.
Any unscoped bound action, @_ <- action@,
also gets bonded to the pattern,
but being unscoped means it isn't added to the context.
If all bound actions are unscoped,
and filtration & failure handling aren't used,
then a `CtxGrammar` can be rewritten as a `Grammar` since it is context-free.
We can't generate a `RegBnf` from a `CtxGrammar` since the `rule`s
aren't static, but dynamic and contextual.
We can generate parsers and printers as expected.

>>> [vec | (vec, "") <- parseG lenvecGrammar "3;1,2,3"] :: [LenVec]
[LenVec {length = 3, vector = [1,2,3]}]
>>> [vec | (vec, "") <- parseG lenvecGrammar "0;1,2,3"] :: [LenVec]
[]
>>> [pr "" | pr <- printG lenvecGrammar (LenVec 2 [6,7])] :: [String]
["2;6,7"]
>>> [pr "" | pr <- printG lenvecGrammar (LenVec 200 [100])] :: [String]
[]

In addition to context-sensitivity via `Monadic` combinators,
`CtxGrammar`s add unrestricted filtration to `Grammar`s.
The `satisfy` combinator is an unrestricted token filter.
And the `satisfied` pattern is used together with the `Choice` &
`Data.Profunctor.Cochoice` applicator `>?<` for unrestricted filtration.

>>> :{
palindromeG :: CtxGrammar Char String
palindromeG = rule "palindrome" $
  satisfied (\wrd -> reverse wrd == wrd) >?< manyP (anyToken @Char)
:}

>>> [pal | word <- ["racecar", "word"], (pal, "") <- parseG palindromeG word]
["racecar"]

Since `CtxGrammar`s are embedded in Haskell,
permitting computable predicates,
and `Filtrator` has a default definition for `Monadic` `Alternator`s,
the context-sensitivity of `CtxGrammar` implies
unrestricted filtration of grammars by computable predicates,
which can recognize the larger class of recursively enumerable languages.

Finally, `CtxGrammar`s support failure reporting and backtracking.
This has no effect on `printG`, `parseG` or `unparseG`;
but it effects `parsecG` and `unparsecG`.
For context, an @LL@ grammar can be (un)parsed by an @LL@ parser.
An @LL@ parser (un)parses from left to right,
and constucts leftmost derivations.
An @LL(k)@ parser can look @k@ tokens ahead.
`Parsor` is an @LL(∞)@ parser.
`Parsector` is an @LL(1)@ parser.
The backtracking `try` combinator
restores full lookahead to `Parsector`.
Since both `Parsor` & `Parsector` are @LL@ parsers they
diverge if the `CtxGrammar` they're run on is left-recursive.

>>> parsecG (rule "foo" (fail "bar") <|> fail "baz") "abc"
ParsecState {parsecLooked = False, parsecOffset = 0, parsecStream = "abc", parsecFailure = ParsecFailure {parsecExpect = TokenClass (OneOf (fromList "")), parsecLabels = [Node {rootLabel = "foo", subForest = [Node {rootLabel = "bar", subForest = []}]},Node {rootLabel = "baz", subForest = []}]}, parsecResult = Nothing}

>>> parsecG (manyP (token 'a') >*< asIn @Char DecimalNumber) "aaab"
ParsecState {parsecLooked = True, parsecOffset = 3, parsecStream = "b", parsecFailure = ParsecFailure {parsecExpect = TokenClass (Alternate (TokenClass (OneOf (fromList "a"))) (TokenClass (NotOneOf (fromList "") (AndAsIn DecimalNumber)))), parsecLabels = []}, parsecResult = Nothing}

>>> unparsecG (tokens "abc") "abx" ""
ParsecState {parsecLooked = True, parsecOffset = 2, parsecStream = "ab", parsecFailure = ParsecFailure {parsecExpect = TokenClass (OneOf (fromList "c")), parsecLabels = []}, parsecResult = Nothing}

-}
type CtxGrammar token a = forall p.
  ( Lexical token p
  , Alternator p
  , Filtrator p
  , MonadicTry p
  ) => p a a

{- |
`Lexical` combinators include `terminal` symbols,
`Tokenized` combinators and `tokenClass`es.
-}
type Lexical token p =
  ( forall x y. (x ~ (), y ~ ()) => TerminalSymbol token (p x y)
  , forall x y. (x ~ token, y ~ token) => TokenAlgebra token (p x y)
  ) :: Constraint

{- | `RegString`s are an embedded domain specific language
of regular expression strings.

Since they are strings, they have a string-like interface.

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
RegExam (Alternate (Sequence (RegExam (OneOf (fromList "a"))) (RegExam (OneOf (fromList "b")))) (RegExam (OneOf (fromList "c"))))

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

A `RegBnf` consists of a distinguished `RegString` "start" rule,
and a set of named `RegString` `rule`s.

>>> putStringLn (rule "baz" (terminal "foo" >|< terminal "bar") :: RegBnf)
{start} = \q{baz}
{baz} = foo|bar

Like `RegString`s they have a string-like interface.

>>> let bnf = fromString "{start} = foo|bar" :: RegBnf
>>> putStringLn bnf
{start} = foo|bar
>>> bnf
"{start} = foo|bar"
>>> :type toList bnf
toList bnf :: [Char]

`RegBnf`s can be generated from context-free `Grammar`s with `regbnfG`.

>>> :type regbnfG regbnfGrammar
regbnfG regbnfGrammar :: RegBnf

Like `RegString`s, `RegBnf`s can be constructed using
`Lexical`, `Monoid` and `KleeneStarAlgebra` combinators.
But they also support `BackusNaurForm` `rule`s and `ruleRec`s.

>>> putStringLn (rule "baz" (bnf >|< terminal "baz"))
{start} = \q{baz}
{baz} = foo|bar|baz
>>> putStringLn (ruleRec "∞-loop" (\x -> x) :: RegBnf)
{start} = \q{∞-loop}
{∞-loop} = \q{∞-loop}
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
{atom} = \\q\q{nonterminal}|\q{class}|\(\q{regex}\)
{category} = Ll|Lu|Lt|Lm|Lo|Mn|Mc|Me|Nd|Nl|No|Pc|Pd|Ps|Pe|Pi|Pf|Po|Sm|Sc|Sk|So|Zs|Zl|Zp|Cc|Cf|Cs|Co|Cn
{char} = [^\(\)\*\+\?\[\\\]\^\{\|\}\P{Cc}]|\\\q{char-escaped}
{char-control} = NUL|SOH|STX|ETX|EOT|ENQ|ACK|BEL|BS|HT|LF|VT|FF|CR|SO|SI|DLE|DC1|DC2|DC3|DC4|NAK|SYN|ETB|CAN|EM|SUB|ESC|FS|GS|RS|US|DEL|PAD|HOP|BPH|NBH|IND|NEL|SSA|ESA|HTS|HTJ|VTS|PLD|PLU|RI|SS2|SS3|DCS|PU1|PU2|STS|CCH|MW|SPA|EPA|SOS|SGCI|SCI|CSI|ST|OSC|PM|APC
{char-escaped} = [\(\)\*\+\?\[\\\]\^\{\|\}]|\q{char-control}
{class} = \q{class-one-of}|\q{class-not-one-of}
{class-category} = \\p\{\q{category}\}|\\P\{(\q{category}(\|\q{category})*)\}
{class-not-one-of} = \q{class-category}|\[\^\q{char}*(\q{class-category}?\])
{class-one-of} = \q{char}|\[\q{char}*\]
{expression} = \q{atom}\?|\q{atom}\*|\q{atom}\+|\q{atom}
{nonterminal} = \{\q{char}*\}
{regex} = \q{alternate}
{sequence} = \q{expression}*
-}
regexGrammar :: Grammar Char RegString
regexGrammar = _RegString >~ ruleRec "regex" altG
  where
    altG rex = rule "alternate" $
      chain1 Left (_RegExam . _Alternate) (sepWith "|") (seqG rex)

    seqG rex = rule "sequence" $
      chain Left _Sequence _SeqEmpty noSep (exprG rex)

    exprG rex = rule "expression" $ choice
      [ _KleeneOpt >? atomG rex *< terminal "?"
      , _KleeneStar >? atomG rex *< terminal "*"
      , _KleenePlus >? atomG rex *< terminal "+"
      , atomG rex
      ]

    atomG rex = rule "atom" $ choice
      [ _NonTerminal >? terminal "\\q" >* nonterminalG
      , _RegExam >? classG
      , terminal "(" >* rex *< terminal ")"
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

    classG = rule "class" $ choice
      [ _OneOf >? classOneOfG
      , _NotOneOf >? classNotOneOfG
      ]

    classCatG = rule "class-category" $ choice
      [ _AndAsIn >? terminal "\\p{" >* categoryG *< terminal "}"
      , _AndNotAsIn >? several1
          (sepWith "|" & beginWith "\\P{" & endWith "}")
          categoryG
      ]

    classOneOfG = rule "class-one-of" $ choice
      [ onlyOne charG
      , terminal "[" >* several noSep charG *< terminal "]"
      ]

    classNotOneOfG = rule "class-not-one-of" $ choice
      [ asEmpty >*< classCatG
      , terminal "[^" >* several noSep charG >*<
          optionP (_AndNotAsIn . _Empty) classCatG *< terminal "]"
      ]

nonterminalG :: Grammar Char String
nonterminalG = rule "nonterminal" $
  terminal "{" >* manyP charG *< terminal "}"

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
{atom} = \\q\q{nonterminal}|\q{class}|\(\q{regex}\)
{category} = Ll|Lu|Lt|Lm|Lo|Mn|Mc|Me|Nd|Nl|No|Pc|Pd|Ps|Pe|Pi|Pf|Po|Sm|Sc|Sk|So|Zs|Zl|Zp|Cc|Cf|Cs|Co|Cn
{char} = [^\(\)\*\+\?\[\\\]\^\{\|\}\P{Cc}]|\\\q{char-escaped}
{char-control} = NUL|SOH|STX|ETX|EOT|ENQ|ACK|BEL|BS|HT|LF|VT|FF|CR|SO|SI|DLE|DC1|DC2|DC3|DC4|NAK|SYN|ETB|CAN|EM|SUB|ESC|FS|GS|RS|US|DEL|PAD|HOP|BPH|NBH|IND|NEL|SSA|ESA|HTS|HTJ|VTS|PLD|PLU|RI|SS2|SS3|DCS|PU1|PU2|STS|CCH|MW|SPA|EPA|SOS|SGCI|SCI|CSI|ST|OSC|PM|APC
{char-escaped} = [\(\)\*\+\?\[\\\]\^\{\|\}]|\q{char-control}
{class} = \q{class-one-of}|\q{class-not-one-of}
{class-category} = \\p\{\q{category}\}|\\P\{(\q{category}(\|\q{category})*)\}
{class-not-one-of} = \q{class-category}|\[\^\q{char}*(\q{class-category}?\])
{class-one-of} = \q{char}|\[\q{char}*\]
{expression} = \q{atom}\?|\q{atom}\*|\q{atom}\+|\q{atom}
{nonterminal} = \{\q{char}*\}
{regbnf} = \{start\} = \q{regex}(\LF\q{nonterminal}( = )\q{regex})*
{regex} = \q{alternate}
{sequence} = \q{expression}*
-}
regbnfGrammar :: Grammar Char RegBnf
regbnfGrammar = rule "regbnf" $ _RegBnf . _Bnf >~
  terminal "{start} = " >* regexGrammar >*< several noSep
    (terminal "\n" >* nonterminalG *< terminal " = " >*< regexGrammar)


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

{- | Compile a `Grammar` into a `Transducer`.

>>> let regexMachine = transducerG @Char regexGrammar

A transducer is a form of finite state machine,
usable as an intermediary for further generators like
`=~`, `expectNext`, `languageSample`, `parseForest` & `unreachableRules`.

>>> import Test.QuickCheck
>>> let regexLang = languageSample @Char regexMachine
>>> words100 <- generate (take 100 <$> regexLang)
>>> quickCheck (property (all (=~ regexMachine) words100))
+++ OK, passed 1 test.
>>> import Control.Monad.State
>>> import System.Random
>>> let gen = mkStdGen 69
>>> evalState (take 15 <$> regexLang) gen
["","|","\776269","()","[]","\\[","||","|\249908","\770923*","\1008821+","\318904?","\845807|","\477898\1026934","()*","()+"]

>>> import Data.Tree (drawForest)

@>>> let (forest, _) = parseForest regexMachine "xy|z" in putStr (drawForest (map (fmap show) forest))
("regex",0,4,"xy|z")
|
`- ("alternate",0,4,"xy|z")
   |
   +- ("sequence",0,2,"xy")
   |  |
   |  +- ("expression",0,1,"x")
   |  |  |
   |  |  `- ("atom",0,1,"x")
   |  |     |
   |  |     `- ("class",0,1,"x")
   |  |        |
   |  |        `- ("class-one-of",0,1,"x")
   |  |           |
   |  |           `- ("char",0,1,"x")
   |  |
   |  `- ("expression",1,2,"y")
   |     |
   |     `- ("atom",1,2,"y")
   |        |
   |        `- ("class",1,2,"y")
   |           |
   |           `- ("class-one-of",1,2,"y")
   |              |
   |              `- ("char",1,2,"y")
   |
   `- ("sequence",3,4,"z")
      |
      `- ("expression",3,4,"z")
         |
         `- ("atom",3,4,"z")
            |
            `- ("class",3,4,"z")
               |
               `- ("class-one-of",3,4,"z")
                  |
                  `- ("char",3,4,"z")
@

-}
transducerG :: Categorized token => Grammar token a -> Transducer token
transducerG bnf = transducer (runGrammor bnf)

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

{- | `parseG` generates a parser from a @LL(∞)@ `CtxGrammar`.
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

{- | `unparseG` generates a printer from a @LL(∞)@ `CtxGrammar`.
Since both `RegGrammar`s and context-free `Grammar`s are `CtxGrammar`s,
the type system will allow `unparseG` to be applied to them.
Running the printer on a syntax value and an input string
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

{- | `parsecG` generates a parser from a @LL(1)@ `CtxGrammar`,
with `try` for restoring full @LL(∞)@ lookahead.
Since both `RegGrammar`s and context-free `Grammar`s are `CtxGrammar`s,
the type system will allow `parsecG` to be applied to them.
Running the parser on an input string value `uncons`es
tokens from the beginning of an input string from left to right,
returning `parsecResult` as `Nothing` on failure or `Just`
an output syntax value, with parse failure stored in `parsecFailure`,
and a remaining output `parsecStream`.
-}
parsecG
  :: (Cons string string token token, Snoc string string token token)
  => (Item string ~ token, Categorized token)
  => CtxGrammar token a
  -> string {- ^ input -}
  -> ParsecState string a
parsecG parsector = parsecP parsector

{- | `unparsecG` generates a printer from a @LL(1)@ `CtxGrammar`,
with `try` for restoring full @LL(∞)@ lookahead.
Since both `RegGrammar`s and context-free `Grammar`s are `CtxGrammar`s,
the type system will allow `unparsecG` to be applied to them.
Running the printer on a syntax value and an input string
`snoc`s tokens at the end of the string, from left to right,
returning `parsecResult` as `Nothing` on failure or `Just`
the input syntax value, with print success stored in `parsecStream`.
-}
unparsecG
  :: (Cons string string token token, Snoc string string token token)
  => (Item string ~ token, Categorized token)
  => CtxGrammar token a
  -> a {- ^ syntax -}
  -> string {- ^ input -}
  -> ParsecState string a
unparsecG parsector = unparsecP parsector

{- | Generate any `Applicative` parser backend
from a `Grammar` with `applicativeG`.
It works the same way as `monadG`,
for parsers without `Monad` instances.
That permits backends to use algorithms
that can only parse context-free `Grammar`s.
-}
applicativeG
  :: ( Alternative f
     , TokenAlgebra token (f token)
     , TerminalSymbol token (f ())
     , forall x. BackusNaurForm (f x)
     )
  => Grammar token a -- ^ context-free grammar
  -> f a
applicativeG joker = runJoker joker

{- | Generate a `ReadP` backend from a `CtxGrammar` `Char`. -}
readG :: CtxGrammar Char a -> ReadP a
readG joker = monadG joker

{- | Generate any parser `Monad` backend
from a `CtxGrammar` with `monadG`.
Let's see how to do this without orphan instances,
using the Megaparsec library.

@
import qualified Text.Megaparsec as M
import qualified Text.Megaparsec.Char as M
import Control.Lens.Grammar

newtype WrapMega a = WrapMega {unwrapMega :: M.Parsec String String a}
  deriving newtype
    ( Functor, Applicative, Alternative
    , Monad, MonadPlus, MonadFail
    )
instance TerminalSymbol Char (WrapMega ()) where
  terminal str = WrapMega (M.chunk str *> pure ())
instance TokenAlgebra Char (WrapMega Char) where
  tokenClass exam = WrapMega $ M.label (show exam) (M.satisfy (tokenClass exam))
instance Tokenized Char (WrapMega Char) where
  anyToken = WrapMega M.anySingle
  token = WrapMega . M.single
  oneOf = WrapMega . M.oneOf
  notOneOf = WrapMega . M.noneOf
  asIn cat = WrapMega $ M.label ("in category " ++ show cat) (M.satisfy (asIn cat))
  notAsIn cat = WrapMega $ M.label ("not in category " ++ show cat) (M.satisfy (notAsIn cat))
instance BackusNaurForm (WrapMega a) where
  rule lbl (WrapMega p) = WrapMega (M.label lbl p)
  ruleRec lbl = rule lbl . fix
instance Filterable WrapMega where
  catMaybes m = m >>= maybe (fail "unrestricted filtration") pure
instance MonadTry WrapMega where
  try (WrapMega p) = WrapMega (M.try p)

megaparsecG
  :: CtxGrammar Char a
  -> M.Parsec String String a
megaparsecG gram = unwrapMega (monadG gram)
@

-}
monadG
  :: ( MonadTry m
     , TokenAlgebra token (m token)
     , TerminalSymbol token (m ())
     )
  => CtxGrammar token a -- ^ context-sensitive grammar
  -> m a
monadG joker = runJoker joker

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
    . readP_to_S (readG regexGrammar)
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
    . readP_to_S (readG regbnfGrammar)
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

data DecimalDigit
  = Dec0 | Dec1 | Dec2 | Dec3 | Dec4
  | Dec5 | Dec6 | Dec7 | Dec8 | Dec9
  deriving stock (Eq, Ord, Show, Read)

data OctalDigit
  = Oct0 | Oct1 | Oct2 | Oct3
  | Oct4 | Oct5 | Oct6 | Oct7
  deriving stock (Eq, Ord, Show, Read)

data HexDigit
  = Hex0 | Hex1 | Hex2 | Hex3 | Hex4 | Hex5 | Hex6 | Hex7
  | Hex8 | Hex9 | HexA | HexB | HexC | HexD | HexE | HexF
  deriving stock (Eq, Ord, Show, Read)

data NaturalSyntax
  = NaturalDecimal [DecimalDigit]
  | NaturalOctal [OctalDigit]
  | NaturalHexadecimal [HexDigit]
  deriving stock (Eq, Ord, Show, Read)
makeNestedPrisms ''NaturalSyntax

decimalDigitValue :: DecimalDigit -> Natural
decimalDigitValue = \case
  Dec0 -> 0; Dec1 -> 1; Dec2 -> 2; Dec3 -> 3; Dec4 -> 4
  Dec5 -> 5; Dec6 -> 6; Dec7 -> 7; Dec8 -> 8; Dec9 -> 9

octalDigitValue :: OctalDigit -> Natural
octalDigitValue = \case
  Oct0 -> 0; Oct1 -> 1; Oct2 -> 2; Oct3 -> 3
  Oct4 -> 4; Oct5 -> 5; Oct6 -> 6; Oct7 -> 7

hexDigitValue :: HexDigit -> Natural
hexDigitValue = \case
  Hex0 -> 0;  Hex1 -> 1;  Hex2 -> 2;  Hex3 -> 3
  Hex4 -> 4;  Hex5 -> 5;  Hex6 -> 6;  Hex7 -> 7
  Hex8 -> 8;  Hex9 -> 9;  HexA -> 10; HexB -> 11
  HexC -> 12; HexD -> 13; HexE -> 14; HexF -> 15

digitsToNatural :: (digit -> Natural) -> Natural -> [digit] -> Natural
digitsToNatural value base = foldl' (\acc d -> acc * base + value d) 0

naturalToDigits :: (Natural -> digit) -> digit -> Natural -> Natural -> [digit]
naturalToDigits fromValue zero base = \case
  0 -> [zero]
  n -> reverse (goDigits n)
  where
    goDigits 0 = []
    goDigits m = let (q, r) = m `divMod` base in fromValue r : goDigits q

natDecimalDigit :: Natural -> DecimalDigit
natDecimalDigit = \case
  0 -> Dec0; 1 -> Dec1; 2 -> Dec2; 3 -> Dec3; 4 -> Dec4
  5 -> Dec5; 6 -> Dec6; 7 -> Dec7; 8 -> Dec8; 9 -> Dec9
  n -> natDecimalDigit (n `mod` 10)

natOctalDigit :: Natural -> OctalDigit
natOctalDigit = \case
  0 -> Oct0; 1 -> Oct1; 2 -> Oct2; 3 -> Oct3
  4 -> Oct4; 5 -> Oct5; 6 -> Oct6; 7 -> Oct7
  n -> natOctalDigit (n `mod` 8)

natHexDigit :: Natural -> HexDigit
natHexDigit = \case
  0 -> Hex0;  1 -> Hex1;  2 -> Hex2;  3 -> Hex3
  4 -> Hex4;  5 -> Hex5;  6 -> Hex6;  7 -> Hex7
  8 -> Hex8;  9 -> Hex9;  10 -> HexA; 11 -> HexB
  12 -> HexC; 13 -> HexD; 14 -> HexE; 15 -> HexF
  n -> natHexDigit (n `mod` 16)

naturalOctal :: Natural -> NaturalSyntax
naturalOctal = NaturalOctal . naturalToDigits natOctalDigit Oct0 8

naturalHexadecimal :: Natural -> NaturalSyntax
naturalHexadecimal = NaturalHexadecimal . naturalToDigits natHexDigit Hex0 16

_NaturalSyntax :: Iso' Natural NaturalSyntax
_NaturalSyntax = iso
  (NaturalDecimal . naturalToDigits natDecimalDigit Dec0 10)
  naturalSyntaxValue
  where
    naturalSyntaxValue (NaturalDecimal ds) = digitsToNatural decimalDigitValue 10 ds
    naturalSyntaxValue (NaturalOctal ds) = digitsToNatural octalDigitValue 8 ds
    naturalSyntaxValue (NaturalHexadecimal ds) = digitsToNatural hexDigitValue 16 ds

decimalDigitG :: Grammar Char DecimalDigit
decimalDigitG = rule "decimal-digit" $ choice
  [ only Dec0 >? terminal "0"
  , only Dec1 >? terminal "1"
  , only Dec2 >? terminal "2"
  , only Dec3 >? terminal "3"
  , only Dec4 >? terminal "4"
  , only Dec5 >? terminal "5"
  , only Dec6 >? terminal "6"
  , only Dec7 >? terminal "7"
  , only Dec8 >? terminal "8"
  , only Dec9 >? terminal "9"
  ]

octalDigitG :: Grammar Char OctalDigit
octalDigitG = rule "octal-digit" $ choice
  [ only Oct0 >? terminal "0"
  , only Oct1 >? terminal "1"
  , only Oct2 >? terminal "2"
  , only Oct3 >? terminal "3"
  , only Oct4 >? terminal "4"
  , only Oct5 >? terminal "5"
  , only Oct6 >? terminal "6"
  , only Oct7 >? terminal "7"
  ]

hexDigitG :: Grammar Char HexDigit
hexDigitG = rule "hex-digit" $ choice
  [ only Hex0 >? terminal "0"
  , only Hex1 >? terminal "1"
  , only Hex2 >? terminal "2"
  , only Hex3 >? terminal "3"
  , only Hex4 >? terminal "4"
  , only Hex5 >? terminal "5"
  , only Hex6 >? terminal "6"
  , only Hex7 >? terminal "7"
  , only Hex8 >? terminal "8"
  , only Hex9 >? terminal "9"
  , only HexA >? (terminal "a" <|> terminal "A")
  , only HexB >? (terminal "b" <|> terminal "B")
  , only HexC >? (terminal "c" <|> terminal "C")
  , only HexD >? (terminal "d" <|> terminal "D")
  , only HexE >? (terminal "e" <|> terminal "E")
  , only HexF >? (terminal "f" <|> terminal "F")
  ]

naturalSyntaxGrammar :: Grammar Char NaturalSyntax
naturalSyntaxGrammar = rule "natural" $ choice
  [ _NaturalHexadecimal >? (terminal "0x" <|> terminal "0X") >* someP hexDigitG
  , _NaturalOctal >? (terminal "0o" <|> terminal "0O") >* someP octalDigitG
  , _NaturalDecimal >? someP decimalDigitG
  ]

naturalGrammar :: Grammar Char Natural
naturalGrammar = _NaturalSyntax >~ naturalSyntaxGrammar

{- | `Sign` marks whether an `IntegerSyntax` term is negative -- present
as a leading @-@ -- or not.
-}
data Sign = NonNegative | Negative
  deriving stock (Eq, Ord, Show, Read)

{- | `IntegerSyntax` extends `NaturalSyntax` with an optional leading
@-@, mirroring how `Read` `Integer` reads: an optional sign, followed
by exactly the same decimal\/octal\/hexadecimal syntax as `Natural`
(GHC's `Read` also tolerates whitespace between the @-@ and the
digits, /e.g./ @read \"-  5\" :: Integer@ is @-5@; `integerGrammar`,
being an exact structural grammar like the rest of this module, does
not).

>>> reads "-0x2A" :: [(Integer, String)]
[(-42,"")]
>>> reads "+5" :: [(Integer, String)]
[]

There's no @NonNegative@ analogue of the leading @-@: a leading @+@ is
not part of GHC's numeral syntax at all, so @IntegerSyntax@ has
nothing to store for it -- `NonNegative` is simply the absence of a sign.
-}
data IntegerSyntax = IntegerSyntax Sign NaturalSyntax
  deriving stock (Eq, Ord, Show, Read)

-- | Apply a `Sign` to a number.
signed :: Num a => Sign -> a -> a
signed NonNegative = id
signed Negative = negate

{- | `_IntegerSyntax` is an /improper/ `Iso'`, for the same reason
`_NaturalSyntax` is: going from `Integer` to `IntegerSyntax` and back
always recovers the original value (the forward direction always
picks `NonNegative` for @0@, mirroring `show (negate 0 :: Integer) = "0"`),
but an `IntegerSyntax` term with leading zeroes, or a redundant
`Negative` sign on @0@, is normalized away on the round trip.

>>> view _IntegerSyntax (-42)
IntegerSyntax Negative (NaturalDecimal [Dec4,Dec2])
>>> IntegerSyntax Negative (NaturalDecimal [Dec0]) ^. from _IntegerSyntax
0
-}
_IntegerSyntax :: Iso' Integer IntegerSyntax
_IntegerSyntax = iso
  (\i -> IntegerSyntax
    (if i < 0 then Negative else NonNegative)
    (view _NaturalSyntax (fromInteger (abs i))))
  (\(IntegerSyntax sign nat) -> signed sign (toInteger (nat ^. from _NaturalSyntax)))

signG :: Grammar Char Sign
signG = rule "sign" $ optionP (only NonNegative) (only Negative >? terminal "-")

{- | Like `signG`, but also accepts (and never prints) a leading @+@ --
used for the exponent of `FloatingSyntax`, since GHC's `Read` accepts
/e.g./ @1.5e+10@ even though a leading @+@ is never part of `show`'s
output.
-}
exponentSignG :: Grammar Char Sign
exponentSignG = rule "exponent-sign" $
  optionP (only NonNegative) (only Negative >? terminal "-")
  <|> (only NonNegative >? terminal "+")

{- | `integerGrammar` is a context-free `Grammar` for `Integer`s,
following the syntax described at `IntegerSyntax`: an optional leading
@-@, then exactly `naturalSyntaxGrammar`.

>>> [i | (i, "") <- parseG integerGrammar "-42"]
[-42]
>>> [i | (i, "") <- parseG integerGrammar "-0x2A"]
[-42]
>>> ($ "") <$> printG integerGrammar (-42) :: Maybe String
Just "-42"
-}
integerGrammar :: Grammar Char Integer
integerGrammar = _IntegerSyntax >~ rule "integer"
  ( iso (\(IntegerSyntax s n) -> (s, n)) (\(s, n) -> IntegerSyntax s n)
    >~ (signG >*< naturalSyntaxGrammar)
  )

{- | `FloatingSyntax` reflects how GHC lexes & shows `Float`\/`Double`
literals. Per the
[Haskell Report's lexical syntax](https://www.haskell.org/onlinereport/haskell2010/haskellch2.html#x7-160002.5)
for @float@ tokens, a floating-point literal is an optional leading
@-@, then decimal digits, then /either/ a @.@ followed by more decimal
digits, /or/ an exponent (@e@\/@E@, an optional sign, then decimal
digits), /or both/ -- /e.g./ @1.5@, @1e10@, @1.5e-3@. `Read` is more
permissive still: unlike the plain @float@ token, it also accepts a
bare integer with neither a @.@ nor an exponent (@read \"1\" ::
Double@ is @1.0@), and it accepts @NaN@ & @Infinity@\/@-Infinity@,
`show`'s renderings of the non-finite `Float`\/`Double` values.

>>> reads "1e10" :: [(Double, String)]
[(1.0e10,"")]
>>> reads "1" :: [(Double, String)]
[(1.0,"")]
>>> reads "Infinity" :: [(Double, String)]
[(Infinity,"")]

GHC's `HexFloatLiterals` extension adds a fourth, @0x@-prefixed
hexadecimal-mantissa\/binary-exponent syntax (/e.g./ @0x1p4@) for
source code literals; like `BinaryLiterals` for `NaturalSyntax`, that
syntax is a compile-time desugaring, not part of `Read`:

>>> reads "0x1p4" :: [(Double, String)]
[(1.0,"p4")]

only the leading @0x1@ (hexadecimal @1@) is consumed. So
`FloatingSyntax` has no hex-float branch.
-}
data FloatingSyntax
  = FloatingDecimal
      Sign               -- ^ overall sign
      [DecimalDigit]     -- ^ digits before the decimal point, at least one
      (Maybe [DecimalDigit])
        -- ^ digits after a @.@, at least one when the @.@ is present
      (Maybe (Sign, [DecimalDigit]))
        -- ^ @e@\/@E@, then a sign & at least one digit, when present
  | FloatingNaN
  | FloatingInfinity Sign
  deriving stock (Eq, Ord, Show, Read)
makeNestedPrisms ''FloatingSyntax

{- | Fold a floating mantissa\/exponent's digits into the `Rational`
they denote. Like `digitsToNatural`, this is plain fixed-point
arithmetic -- no `read`, `Numeric.readFloat` or otherwise -- built on
`%` and `(^^)`. Takes the `FloatingDecimal` fields directly, rather
than a `FloatingSyntax`, so that it's total: `FloatingNaN` &
`FloatingInfinity` don't denote a `Rational` at all, and are handled
separately by `fromFloatingSyntax`.
-}
floatingSyntaxRational
  :: Sign -> [DecimalDigit] -> Maybe [DecimalDigit] -> Maybe (Sign, [DecimalDigit])
  -> Rational
floatingSyntaxRational sign intDs fracDs mExp =
  signed sign (magnitude * (10 ^^ expVal))
  where
    intVal = toInteger (digitsToNatural decimalDigitValue 10 intDs)
    (fracVal, fracLen) = case fracDs of
      Nothing -> (0, 0)
      Just ds -> (toInteger (digitsToNatural decimalDigitValue 10 ds), length ds)
    mantissa = intVal * 10 ^ fracLen + fracVal
    magnitude = mantissa % (10 ^ fracLen)
    expVal = case mExp of
      Nothing -> 0
      Just (esign, eds) -> signed esign (toInteger (digitsToNatural decimalDigitValue 10 eds))

-- | The `RealFloat` value a `FloatingSyntax` denotes.
fromFloatingSyntax :: RealFloat a => FloatingSyntax -> a
fromFloatingSyntax FloatingNaN = 0 / 0
fromFloatingSyntax (FloatingInfinity NonNegative) = 1 / 0
fromFloatingSyntax (FloatingInfinity Negative) = negate (1 / 0)
fromFloatingSyntax (FloatingDecimal sign intDs fracDs mExp) =
  fromRational (floatingSyntaxRational sign intDs fracDs mExp)

{- | Render a `RealFloat` value's significant decimal digits @ds@ &
decimal exponent @e@ -- a `Numeric.floatToDigits` pair, meaning the
value is @0.ds * 10^e@ -- as a `FloatingSyntax`, replicating GHC's own
choice (in @GHC.Float.formatRealFloatAlt@) between plain decimal &
scientific notation: scientific when @e < 0 || e > 7@, plain otherwise.
`floatToDigits` is the numeric mantissa\/exponent decomposition
`RealFloat` itself is built on -- the same primitive `show` uses --
so what's hand-rolled here is exactly the string-shaped part: the
`FFGeneric` threshold, digit padding & the trailing @.0@, not the
digit generation itself.
-}
digitsToFloatingSyntax :: Sign -> ([Int], Int) -> FloatingSyntax
digitsToFloatingSyntax sign (is, e)
  | e < 0 || e > 7 = scientificForm
  | otherwise = fixedForm
  where
    ds = map (natDecimalDigit . fromIntegral) is

    fixedForm
      | e <= 0 = FloatingDecimal sign [Dec0]
          (Just (replicate (negate e) Dec0 ++ ds)) Nothing
      | otherwise =
          let
            (intDs, fracDs0) = splitAt e ds
            intDs' = intDs ++ replicate (e - length intDs) Dec0
            fracDs = if null fracDs0 then [Dec0] else fracDs0
          in
            FloatingDecimal sign intDs' (Just fracDs) Nothing

    scientificForm =
      let
        (d, ds') = case ds of
          (d0 : rest) -> (d0, rest)
          [] -> (Dec0, [])
        frac = if null ds' then [Dec0] else ds'
        expn = e - 1
        expSign = if expn < 0 then Negative else NonNegative
        expDigits = naturalToDigits natDecimalDigit Dec0 10 (fromInteger (abs (toInteger expn)))
      in
        FloatingDecimal sign [d] (Just frac) (Just (expSign, expDigits))

{- | `_FloatingSyntax` is an /improper/ `Iso'`, for the same reason
`_NaturalSyntax` & `_IntegerSyntax` are: the forward direction always
picks the canonical form `show` would produce (plain decimal or
scientific, per the `digitsToFloatingSyntax` threshold), so going
`RealFloat` value @->@ `FloatingSyntax` @->@ value recovers the
original value, but a `FloatingSyntax` term with, /e.g./, a redundant
@+@ on its exponent, or digits that would print differently, doesn't
round trip the other way.

>>> view _FloatingSyntax (1.5 :: Double)
FloatingDecimal NonNegative [Dec1] (Just [Dec5]) Nothing
>>> view _FloatingSyntax (1.0e10 :: Double)
FloatingDecimal NonNegative [Dec1] (Just [Dec0]) (Just (NonNegative,[Dec1,Dec0]))
-}
_FloatingSyntax :: RealFloat a => Iso' a FloatingSyntax
_FloatingSyntax = iso toFloatingSyntax fromFloatingSyntax
  where
    toFloatingSyntax x
      | isNaN x = FloatingNaN
      | isInfinite x = FloatingInfinity (if x < 0 then Negative else NonNegative)
      | x < 0 || isNegativeZero x =
          digitsToFloatingSyntax Negative (floatToDigits 10 (negate x))
      | otherwise =
          digitsToFloatingSyntax NonNegative (floatToDigits 10 x)

{- | `floatingSyntaxGrammar` follows the syntax described at
`FloatingSyntax`: `NaN`, `NonNegative`\/`Negative` `Infinity`, or a
signed decimal mantissa with an optional fractional part & an
optional signed exponent.
-}
floatingSyntaxGrammar :: Grammar Char FloatingSyntax
floatingSyntaxGrammar = rule "floating" $ choice
  [ _FloatingNaN >? terminal "NaN"
  , _FloatingInfinity >? signG *< terminal "Infinity"
  , _FloatingDecimal >?
      signG >*< someP decimalDigitG >*<
        optionalP (terminal "." >* someP decimalDigitG) >*<
        optionalP ((terminal "e" <|> terminal "E") >* (exponentSignG >*< someP decimalDigitG))
  ]

{- | `doubleGrammar` is a context-free `Grammar` for `Double`s,
following the syntax described at `FloatingSyntax`. It always prints
& unparses exactly as `show` would -- plain decimal or scientific,
matching GHC's own threshold -- since `_FloatingSyntax` normalizes to
that canonical form on its way out, but it parses anything `Read`
does (bar hex-float literals), including bare integers, `NaN` &
`Infinity`.

>>> [x | (x, "") <- parseG doubleGrammar "1.5"]
[1.5]
>>> [x | (x, "") <- parseG doubleGrammar "1e10"]
[1.0e10]
>>> ($ "") <$> printG doubleGrammar (10000000.0 :: Double) :: Maybe String
Just "1.0e7"
>>> ($ "") <$> printG doubleGrammar (1/0 :: Double) :: Maybe String
Just "Infinity"
-}
doubleGrammar :: Grammar Char Double
doubleGrammar = _FloatingSyntax >~ floatingSyntaxGrammar

{- | `floatGrammar` is `doubleGrammar`'s `Float` analogue, sharing
`floatingSyntaxGrammar` & `_FloatingSyntax`; only the final
`fromRational`\/`floatToDigits` precision differs.

>>> ($ "") <$> printG floatGrammar (1.5 :: Float) :: Maybe String
Just "1.5"
-}
floatGrammar :: Grammar Char Float
floatGrammar = _FloatingSyntax >~ floatingSyntaxGrammar
