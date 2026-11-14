{-# LANGUAGE ExplicitNamespaces, RequiredTypeArguments #-}
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
    RegGrammar (..)
  , RegGrammatical
  , regexG
    -- * Context-free grammar
  , Grammar (..)
  , Grammatical
  , regbnfG
  , applicativeG
  , transducerG
    -- * Context-sensitive grammar
  , CtxGrammar (..)
  , CtxGrammatical
  , printG
  , parseG
  , unparseG
  , parsecG
  , unparsecG
  , readG
  , monadG
    -- * Utility
  , putStringLn
    -- * Re-exports
  , module X
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.PartialIso
import Control.Lens.Grammar.BackusNaur
import Control.Lens.Grammar.Machine
import Control.Lens.Grammar.RegEx
import Control.Lens.Grammar.Token
import Control.Lens.Grammar.Symbol
import Data.Bifunctor.Joker
import Data.Bits (Bits, toIntegralSized)
import Data.Char (isDigit)
import Data.Int (Int8, Int16, Int32, Int64)
import Data.Maybe (isJust)
import Data.Monoid.Disjunctive
import Data.Profunctor.Distributor
import Data.Profunctor.Monoidal.Cocartesian
import Data.Profunctor.Filtrator
import Data.Profunctor.Monadic as X
import Data.Profunctor.Monoidal
import Data.Profunctor.Grammar
import Data.Profunctor.Grammar.Parsector
import Data.Word (Word8, Word16, Word32, Word64)
import GHC.Exts
import Numeric.Natural (Natural)
import Prelude hiding (filter)
import Text.ParserCombinators.ReadP (ReadP)
import Witherable

-- Re-exports
import Control.Lens.Cons as X
import Control.Lens.Empty as X
import Control.Lens.Grammar.BackusNaur as X hiding
  (RegGrammatical, Grammatical, CtxGrammatical)
import Control.Lens.Grammar.Analysis as X
import Control.Lens.Grammar.Machine as X
import Control.Lens.Grammar.RegEx as X
import Control.Lens.Grammar.Symbol as X
import Control.Lens.Grammar.Token as X
import Control.Lens.PartialIso as X
import Control.Lens.Bifocal as X
import Control.Lens.Diopter as X
import Control.Lens.Prismoid as X
import Control.Lens.Varifocal as X
import Control.Applicative as X (Alternative (..))
import Control.Monad as X (MonadPlus (..), MonadFail (..))
import Witherable as X (Filterable (..))
import Data.Monoid.Disjunctive as X
import Data.Profunctor.Distributor as X
import Data.Profunctor.Monoidal.Cocartesian as X
import Data.Profunctor.Filtrator as X
import Data.Profunctor.Grammar as X
import Data.Profunctor.Grammar.Parsector as X
import Data.Profunctor.Monoidal as X
import Data.Traversable.Homogeneous as X
import Data.Traversable.Homogeneous.Enumerable as X

-- $setup
-- >>> :set -XRequiredTypeArguments -XExplicitNamespaces -XTypeApplications
-- >>> import Data.String (fromString)
-- >>> import GHC.Exts (toList)

{- |
A regular grammar may be constructed using
`terminal` symbols, `Tokenized` combinators, `tokenClass`es
and `Alternator` combinators.
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
which is used to test this documentation.
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
semverGrammar :: RegGrammatical Char p => p SemVer SemVer
semverGrammar = _SemVer
  >?  numberG
  >*< terminal "." >* numberG
  >*< terminal "." >* numberG
  >*< optionP _Empty (terminal "-" >* identifiersG)
  >*< optionP _Empty (terminal "+" >* identifiersG)
  where
    numberG = iso show read >~ someP (asIn @Char DecimalNumber)
    identifiersG = sepWith "." (atLeast 1) (someP charG)
    charG = asIn LowercaseLetter
      >|< asIn UppercaseLetter
      >|< asIn DecimalNumber
      >|< token '-'
instance CtxGrammar Char SemVer
instance Grammar Char SemVer
instance RegGrammar Char SemVer where regGrammar = semverGrammar
:}

A type's `RegGrammar` instance, here @semverGrammar@, & its `Grammar`
& `CtxGrammar` instances, by default, let generators run it by its type,
a required type argument, @(type SemVer)@ where a constructor shares
its name, & parsers & printers by inference.

Instead of using the constructor @SemVer@ with the `Functor` applicator `<$>`,
we use the optic @_SemVer@ we defined and the `Choice` applicator `>?`;
although, we could have used the `Profunctor` applicator `>~` instead,
because @_SemVer@ is an `Control.Lens.Iso.Iso`.

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
| `empty`    | `falseP`      |
+------------+---------------+
| `<|>`      | `>|<`         |
+------------+---------------+
| @choice@   | `orP`         |
+------------+---------------+
| `many`     | `manyP`       |
+------------+---------------+
| `some`     | `someP`       |
+------------+---------------+
| `optional` | `optionalP`   |
+------------+---------------+

You can generate a regular expression string, a `RegEx`, from a `RegGrammar`
with `Control.Lens.Grammar.regexG`.

>>> putStringLn (regexG (type SemVer))
\p{Nd}+.\p{Nd}+.\p{Nd}+(-(\p{Ll}|\p{Lu}|\p{Nd}|-)+(.(\p{Ll}|\p{Lu}|\p{Nd}|-)+)*)?(\+(\p{Ll}|\p{Lu}|\p{Nd}|-)+(.(\p{Ll}|\p{Lu}|\p{Nd}|-)+)*)?

You can also generate parsers and printers.

>>> [parsed | (parsed, "") <- parseG @SemVer "2.1.5-rc.1+build.123"]
[SemVer {major = 2, minor = 1, patch = 5, preRelease = ["rc","1"], buildMetadata = ["build","123"]}]

Parsing `uncons`es tokens left-to-right, from the beginning of a string.
Unparsing, on the other hand, `snoc`s tokens left-to-right, to the end of a string.

>>> unparseG (SemVer 1 0 0 ["alpha"] []) "SemVer: " :: Maybe String
Just "SemVer: 1.0.0-alpha"

Printing, on the gripping hand, `cons`es tokens right-to-left, to the beginning of a string.

>>> ($ " is the SemVer.") <$> printG (SemVer 1 2 3 [] []) :: Maybe String
Just "1.2.3 is the SemVer."

`Profunctor`ial combinators give us correct-by-construction invertible parsers.
New `RegGrammar` generators can be defined with new `RegGrammatical` instances.
-}
class Grammar token a => RegGrammar token a where
  regGrammar :: RegGrammatical token p => p a a


{- | Context-free `Grammar`s add two capabilities to `RegGrammar`s,
coming from the `BackusNaurForm` interface

* `rule` abstraction,
* and general recursion.

`Control.Lens.Grammar.RegEx.regexGrammar` and
`Control.Lens.Grammar.RegEx.regbnfGrammar` are examples of context-free
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
arithGrammar :: Grammatical Char p => p Arith Arith
arithGrammar = ruleRec "arith" sumG
  where
    sumG arith = rule "sum" $
      sepWith "+" (chain1 Left _Add) (prodG arith)
    prodG arith = rule "product" $
      sepWith "*" (chain1 Left _Mul) (factorG arith)
    factorG arith = rule "factor" $
      numberG >|< terminal "(" >* arith *< terminal ")"
    numberG = rule "number" $
      _Num . iso show read >? someP (asIn @Char DecimalNumber)
instance CtxGrammar Char Arith
instance Grammar Char Arith where grammar = arithGrammar
:}

We can generate grammar strings, printers and parsers from @arithGrammar@.

>>> putStringLn (regbnfG Arith)
{start} = \q{arith}
{arith} = \q{sum}
{factor} = \q{number}|\(\q{arith}\)
{number} = \p{Nd}+
{product} = \q{factor}(\*\q{factor})*
{sum} = \q{product}(\+\q{product})*
>>> [x | (x,"") <- parseG @Arith "1+2*3+4"]
[Add (Add (Num 1) (Mul (Num 2) (Num 3))) (Num 4)]
>>> unparseG (Add (Num 1) (Mul (Num 2) (Num 3))) "" :: Maybe String
Just "1+2*3"
>>> do pr <- printG (Num 69); pure (pr "") :: Maybe String
Just "69"

Operator tables with precedence, like @buildExpressionParser@'s,
are built by `withOperators`. For example, an expression grammar
over natural numbers with a postfix factorial @!@ (binding tightest,
and not required to actually compute a factorial), a right-associative
exponent @^@, a left-associative @*@, and left-associative @+@ & @-@
binding loosest:

>>> :{
data Expr
  = Nat Natural
  | Fac Expr
  | Exp Expr Expr
  | Mul Expr Expr
  | Add Expr Expr
  | Sub Expr Expr
  deriving stock (Eq, Ord, Show, Read)
_Nat :: Prism' Expr Natural
_Nat = prism' Nat (\case Nat n -> Just n; _ -> Nothing)
_Fac :: Prism' Expr Expr
_Fac = prism' Fac (\case Fac x -> Just x; _ -> Nothing)
_Exp, _Mul, _Add, _Sub :: Prism' Expr (Expr, Expr)
_Exp = prism' (uncurry Exp) (\case Exp x y -> Just (x,y); _ -> Nothing)
_Mul = prism' (uncurry Mul) (\case Mul x y -> Just (x,y); _ -> Nothing)
_Add = prism' (uncurry Add) (\case Add x y -> Just (x,y); _ -> Nothing)
_Sub = prism' (uncurry Sub) (\case Sub x y -> Just (x,y); _ -> Nothing)
exprGrammar :: Grammatical Char p => p Expr Expr
exprGrammar = ruleRec "expr" $ \expr ->
  let atom = rule "atom" $ nat >|< terminal "(" >* expr *< terminal ")"
      nat  = rule "nat"  $ _Nat . iso show read >? someP (asIn @Char DecimalNumber)
  in withOperators
    [ [ Postfix _Fac (terminal "!") ]
    , [ Infix RightAssoc _Exp (terminal "^") ]
    , [ Infix LeftAssoc _Mul (terminal "*") ]
    , [ Infix LeftAssoc _Add (terminal "+"), Infix LeftAssoc _Sub (terminal "-") ]
    ] atom
instance CtxGrammar Char Expr
instance Grammar Char Expr where grammar = exprGrammar
:}

The right-associative @^@ groups to the right, @-@ to the left, @*@
binds tighter than @+@, and postfix @!@ binds tighter than @^@:

>>> [e | (e,"") <- parseG @Expr "2^3^2"]
[Exp (Nat 2) (Exp (Nat 3) (Nat 2))]
>>> [e | (e,"") <- parseG @Expr "3-2-1"]
[Sub (Sub (Nat 3) (Nat 2)) (Nat 1)]
>>> [e | (e,"") <- parseG @Expr "2*3+4"]
[Add (Mul (Nat 2) (Nat 3)) (Nat 4)]
>>> [e | (e,"") <- parseG @Expr "2*(3+4)"]
[Mul (Nat 2) (Add (Nat 3) (Nat 4))]
>>> [e | (e,"") <- parseG @Expr "3!"]
[Fac (Nat 3)]
>>> [e | (e,"") <- parseG @Expr "2^3!"]
[Exp (Nat 2) (Fac (Nat 3))]

Being bidirectional, the same grammar prints:

>>> unparseG (Exp (Nat 2) (Exp (Nat 3) (Nat 2))) "" :: Maybe String
Just "2^3^2"
>>> unparseG (Exp (Nat 2) (Fac (Nat 3))) "" :: Maybe String
Just "2^3!"

If all `rule`s are non-recursive, then a `Grammar`
can be rewritten as a `RegGrammar`.
Since Haskell permits general recursion, and `RegGrammar`s are
embedded in Haskell, you can define context-free grammars with them.
But it's recommended to use `Grammar`s for `rule` abstraction
and generator support for `ruleRec`.

-}
class CtxGrammar token a => Grammar token a where
  grammar :: Grammatical token p => p a a
  default grammar :: (RegGrammar token a, Grammatical token p) => p a a
  grammar = regGrammar @token


{- | For context-sensitivity,
the `Monadic` interface is used by importing "Data.Profunctor.Monadic.Do"
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
>>> import qualified Data.Profunctor.Monadic.Do as P
>>> :{
lenvecGrammar :: CtxGrammatical Char p => p LenVec LenVec
lenvecGrammar = _LenVec >? P.do
  let
    numberG = iso show read >~ someP (asIn @Char DecimalNumber)
    vectorG n = sepWith "," (exactly n) numberG
  len <- numberG             -- bonds to _LenVec
  terminal ";"               -- doesn't bond
  vectorG (fromIntegral len) -- bonds to _LenVec
instance CtxGrammar Char LenVec where ctxGrammar = lenvecGrammar
:}

The qualified do-notation changes the signature of
@P.@`Data.Profunctor.Monadic.Do.>>=`,
so that we must apply the constructor pattern @_LenVec@
to the do-block with the `>?` applicator.
Any scoped bound action, @var <- action@,
gets "bonded" to the constructor pattern.
Unbound actions, except for the last action in the do-block,
don't get bonded to the pattern.
The last action does get bonded to the pattern.
Any unscoped bound action, @_ <- action@,
also gets bonded to the pattern,
but being unscoped means it isn't added to the context.
If all bound actions are unscoped,
and filtration & failure handling aren't used,
then a `CtxGrammar` can be rewritten as a `Grammar` since it is context-free.
We can't generate a t'Bnf' from a `CtxGrammar` since the `rule`s
aren't static, but dynamic and contextual.
We can generate parsers and printers as expected.

>>> [vec | (vec, "") <- parseG "3;1,2,3"] :: [LenVec]
[LenVec {length = 3, vector = [1,2,3]}]
>>> [vec | (vec, "") <- parseG "0;1,2,3"] :: [LenVec]
[]
>>> [pr "" | pr <- printG (LenVec 2 [6,7])] :: [String]
["2;6,7"]
>>> [pr "" | pr <- printG (LenVec 200 [100])] :: [String]
[]

In addition to context-sensitivity via `Monadic` combinators,
`CtxGrammar`s add unrestricted filtration to `Grammar`s.
The `satisfy` combinator is an unrestricted token filter.
And the `satisfied` pattern is used together with the `Choice` &
`Data.Profunctor.Cochoice` applicator `>?<` for unrestricted filtration.

>>> :{
palindromeG :: CtxGrammatical Char p => p String String
palindromeG = rule "palindrome" $
  satisfied (\wrd -> reverse wrd == wrd) >?< manyP (anyToken @Char)
:}

>>> [pal | word <- ["racecar", "word"], (pal, "") <- parseP (palindromeG :: Parsor String [] String String) word]
["racecar"]

Since `CtxGrammar`s are embedded in Haskell,
permitting computable predicates,
and `Filtrator` has a default definition for `Monadic` `Alternator`s,
the context-sensitivity of `CtxGrammar` implies
unrestricted filtration of grammars by computable predicates,
which can recognize the larger class of recursively enumerable languages.

Context-sensitivity can also be optical. A `Varifocal` is an optic
whose shape depends on the foci it builds, as no `Bifocal` can,
applied in a `CtxGrammar` by `contextually`,
or on a `MonadicTrans` profunctor, by `contextuallyT`.
A [heredoc](https://en.wikipedia.org/wiki/Here_document)'s lines are its foci,
its tag, its body, & its tag again, `delimitBy` by the first line
equal to the opening tag, a language which isn't context-free.

>>> :{
data Heredoc = Heredoc String [String] deriving (Eq, Show)
heredocG :: CtxGrammatical Char p => p Heredoc Heredoc
heredocG = lined >~ terminal "<<" >* contextually (delimitBy (==)) lineG
  where
    lineG = manyP (notOneOf "\n") *< terminal "\n"
    lined = iso
      (\(Heredoc tag body) -> tag : body ++ [tag])
      (\case
        tag : rest -> Heredoc tag (if null rest then [] else init rest)
        [] -> Heredoc "" [])
instance CtxGrammar Char Heredoc where ctxGrammar = heredocG
:}

>>> [pr "" | pr <- printG (Heredoc "EOF" ["hi"])] :: [String]
["<<EOF\nhi\nEOF\n"]
>>> [h | (h, "") <- parseG @Heredoc "<<EOF\nhi\nEOF\n"]
[Heredoc "EOF" ["hi"]]
>>> parsecResult (parsecG @Heredoc "<<EOF\nhi\nEOF\n")
Just (Heredoc "EOF" ["hi"])
>>> [pr "" | pr <- printG (Heredoc "EOF" ["EOF"])] :: [String]
[]

Finally, `CtxGrammar`s support failure reporting and backtracking.
This has no effect on `Control.Lens.Grammar.printG`,
`Control.Lens.Grammar.parseG` or `Control.Lens.Grammar.unparseG`;
but it affects `Control.Lens.Grammar.parsecG`
and `Control.Lens.Grammar.unparsecG`.
For context, an @LL@ grammar can be (un)parsed by an @LL@ parser.
An @LL@ parser (un)parses from left to right,
and constructs leftmost derivations.
An @LL(k)@ parser can look @k@ tokens ahead.
t'Parsor' is an @LL(∞)@ parser.
t'Parsector' is an @LL(1)@ parser.
The backtracking `try` combinator
restores full lookahead to t'Parsector'.
Since both t'Parsor' & t'Parsector' are @LL@ parsers they
diverge if the `CtxGrammar` they're run on is left-recursive.

>>> parsecP (rule "foo" (fail "bar") >|< fail "baz") "abc"
ParsecState {parsecLooked = False, parsecOffset = 0, parsecStream = "abc", parsecFailure = ParsecFailure {parsecExpect = TokenClass (OneOf (fromList "")), parsecLabels = [Node {rootLabel = "foo", subForest = [Node {rootLabel = "bar", subForest = []}]},Node {rootLabel = "baz", subForest = []}]}, parsecResult = Nothing}

>>> parsecP (manyP (token 'a') >*< asIn @Char DecimalNumber :: Parsector String (String, Char) (String, Char)) "aaab"
ParsecState {parsecLooked = True, parsecOffset = 3, parsecStream = "b", parsecFailure = ParsecFailure {parsecExpect = TokenClass (Alternate (TokenClass (OneOf (fromList "a"))) (TokenClass (NotOneOf (fromList "") (AndAsIn DecimalNumber))) []), parsecLabels = []}, parsecResult = Nothing}

>>> unparsecP (tokens "abc") "abx" ""
ParsecState {parsecLooked = True, parsecOffset = 2, parsecStream = "ab", parsecFailure = ParsecFailure {parsecExpect = TokenClass (OneOf (fromList "c")), parsecLabels = []}, parsecResult = Nothing}

-}
class CtxGrammar token a where
  ctxGrammar :: CtxGrammatical token p => p a a
  default ctxGrammar :: (Grammar token a, CtxGrammatical token p) => p a a
  ctxGrammar = grammar @token



{- | `regexG` generates a `RegEx`pression from a regular grammar,
over any token, a regular expression string over characters.
Since context-free `Grammar`s and `CtxGrammar`s aren't necessarily regular,
the type system will prevent `regexG` from being applied to them.
-}
regexG
  :: forall token. forall a -> (Categorized token, RegGrammar token a)
  => RegEx token
regexG a = runGrammor (regGrammar @token @a)

{- | `regbnfG` generates a t'Bnf' of `RegEx`pressions from a context-free
`Grammar`, over any token, of regular expression strings over characters.
Since `CtxGrammar`s aren't context-free,
the type system will prevent `regbnfG` from being applied to a `CtxGrammar`.
It can apply to a `RegGrammar`.
-}
regbnfG
  :: forall token. forall a -> (Categorized token, Grammar token a)
  => Bnf (RegEx token)
regbnfG a = runGrammor (grammar @token @a)

{- | Compile a `Grammar` into a t'Transducer'.

>>> let regexMachine = transducerG @Char (RegEx Char)

A transducer is a form of finite state machine,
usable as an intermediary for further generators like
`=~`, `expectNext`, `languageSample`, `parseForest` & `unreachableRules`.

>>> import Test.QuickCheck
>>> let regexLang = languageSample @Char regexMachine
>>> words100 <- generate (take 100 <$> regexLang)
>>> quickCheck (property (all (=~ regexMachine) words100))
+++ OK, passed 100 tests.
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
transducerG
  :: forall token. forall a -> (Categorized token, Grammar token a)
  => Transducer token
transducerG a = transducer (runGrammor (grammar @token @a))

{- | `printG` generates a printer from a `CtxGrammar`.
Since both `RegGrammar`s and context-free `Grammar`s are `CtxGrammar`s,
the type system will allow `printG` to be applied to them.
Running the printer on a syntax value returns a function
that `cons`es tokens at the beginning of an input string,
from right to left.
-}
printG
  :: forall a string token m. CtxGrammar token a
  => Cons string string token token
  => (IsList string, Item string ~ token, Categorized token)
  => (Alternative m, Monad m, Filterable m)
  => a {- ^ syntax -}
  -> m (string -> string)
printG = printP (ctxGrammar @token @a)

{- | `parseG` generates a parser from a @LL(∞)@ `CtxGrammar`.
Since both `RegGrammar`s and context-free `Grammar`s are `CtxGrammar`s,
the type system will allow `parseG` to be applied to them.
Running the parser on an input string value `uncons`es
tokens from the beginning of an input string from left to right,
returning a syntax value and the remaining output string.
-}
parseG
  :: forall a string token m. CtxGrammar token a
  => (Cons string string token token, Snoc string string token token)
  => (IsList string, Item string ~ token, Categorized token)
  => (Alternative m, Monad m, Filterable m)
  => string {- ^ input -}
  -> m (a, string)
parseG = parseP (ctxGrammar @token @a)

{- | `unparseG` generates a printer from a @LL(∞)@ `CtxGrammar`.
Since both `RegGrammar`s and context-free `Grammar`s are `CtxGrammar`s,
the type system will allow `unparseG` to be applied to them.
Running the printer on a syntax value and an input string
`snoc`s tokens at the end of the string, from left to right,
returning the output string.
Print to a string with a constant time `snoc`, like a
@Data.Sequence.Seq@, since a list's `snoc` is linear,
making printing to a `String` quadratic.
-}
unparseG
  :: forall a string token m. CtxGrammar token a
  => (Cons string string token token, Snoc string string token token)
  => (IsList string, Item string ~ token, Categorized token)
  => (Alternative m, Monad m, Filterable m)
  => a {- ^ syntax -}
  -> string {- ^ input -}
  -> m string
unparseG = unparseP (ctxGrammar @token @a)

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
  :: forall a string token. CtxGrammar token a
  => (Cons string string token token, Snoc string string token token)
  => (Item string ~ token, Categorized token)
  => string {- ^ input -}
  -> ParsecState string a
parsecG = parsecP (ctxGrammar @token @a)

{- | `unparsecG` generates a printer from a @LL(1)@ `CtxGrammar`,
with `try` for restoring full @LL(∞)@ lookahead.
Since both `RegGrammar`s and context-free `Grammar`s are `CtxGrammar`s,
the type system will allow `unparsecG` to be applied to them.
Running the printer on a syntax value and an input string
`snoc`s tokens at the end of the string, from left to right,
returning `parsecResult` as `Nothing` on failure or `Just`
the input syntax value, with print success stored in `parsecStream`.
Print to a string with a constant time `snoc`, like a
@Data.Sequence.Seq@, since a list's `snoc` is linear,
making printing to a `String` quadratic.
-}
unparsecG
  :: forall a string token. CtxGrammar token a
  => (Cons string string token token, Snoc string string token token)
  => (Item string ~ token, Categorized token)
  => a {- ^ syntax -}
  -> string {- ^ input -}
  -> ParsecState string a
unparsecG = unparsecP (ctxGrammar @token @a)

{- | Generate any `Applicative` parser backend
from a `Grammar` with `applicativeG`.
It works the same way as `monadG`,
for parsers without `Monad` instances.
That permits backends to use algorithms
that can only parse context-free `Grammar`s.
-}
applicativeG
  :: forall token a f.
     ( Grammar token a
     , Alternative f
     , TokenAlgebra token (f token)
     , TerminalSymbol token (f ())
     , forall x. BackusNaurForm (f x)
     , forall x. Tried (f x)
     )
  => f a
applicativeG = runJoker (grammar @token @a)

{- | Generate a `ReadP` backend from a `CtxGrammar` `Char`. -}
readG :: CtxGrammar Char a => ReadP a
readG = monadG @Char

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
instance Ruled (WrapMega a) where
  rule lbl (WrapMega p) = WrapMega (M.label lbl p)
instance BackusNaurForm (WrapMega a)
instance Tried (WrapMega a) where
  try (WrapMega p) = WrapMega (M.try p)
instance Filterable WrapMega where
  catMaybes m = m >>= maybe (fail "unrestricted filtration") pure

megaparsecG :: CtxGrammar Char a => M.Parsec String String a
megaparsecG = unwrapMega (monadG @Char)
@

-}
monadG
  :: forall token a m.
     ( CtxGrammar token a
     , MonadPlus m, MonadFail m, Filterable m
     , forall x. BackusNaurForm (m x)
     , forall x. Tried (m x)
     , TokenAlgebra token (m token)
     , TerminalSymbol token (m ())
     )
  => m a
monadG = runJoker (ctxGrammar @token @a)

{- | `putStringLn` is a utility that generalizes `putStrLn`
to string-like interfaces such as `RegEx` and t'Bnf' of `Char`s.
-}
putStringLn :: (IsList string, Item string ~ Char) => string -> IO ()
putStringLn = putStrLn . toList

-- Base types --

instance CtxGrammar Char Char
instance Grammar Char Char where grammar = rule "Char" (regGrammar @Char)
instance RegGrammar Char Char where regGrammar = anyToken @Char

instance CtxGrammar Char String
instance Grammar Char String where grammar = rule "String" (regGrammar @Char)
instance RegGrammar Char String where regGrammar = manyP (anyToken @Char)

instance CtxGrammar Char Natural
instance Grammar Char Natural where grammar = rule "Natural" (regGrammar @Char)
instance RegGrammar Char Natural where regGrammar = naturalG

instance CtxGrammar Char Integer
instance Grammar Char Integer where grammar = rule "Integer" (regGrammar @Char)
instance RegGrammar Char Integer where regGrammar = integerG

instance CtxGrammar Char Double
instance Grammar Char Double where grammar = rule "Double" (regGrammar @Char)
instance RegGrammar Char Double where regGrammar = floatingG

instance CtxGrammar Char Float
instance Grammar Char Float where grammar = rule "Float" (regGrammar @Char)
instance RegGrammar Char Float where regGrammar = floatingG

{- Sized integers' syntax is `Integer`'s, but a literal out of their range
fails to build, which only a `CtxGrammar`'s `Filtrator` can, so they have
no regular expression or Backus-Naur form. -}
instance CtxGrammar Char Int where ctxGrammar = rule "Int" sizedG
instance CtxGrammar Char Int8 where ctxGrammar = rule "Int8" sizedG
instance CtxGrammar Char Int16 where ctxGrammar = rule "Int16" sizedG
instance CtxGrammar Char Int32 where ctxGrammar = rule "Int32" sizedG
instance CtxGrammar Char Int64 where ctxGrammar = rule "Int64" sizedG
instance CtxGrammar Char Word where ctxGrammar = rule "Word" sizedG
instance CtxGrammar Char Word8 where ctxGrammar = rule "Word8" sizedG
instance CtxGrammar Char Word16 where ctxGrammar = rule "Word16" sizedG
instance CtxGrammar Char Word32 where ctxGrammar = rule "Word32" sizedG
instance CtxGrammar Char Word64 where ctxGrammar = rule "Word64" sizedG

-- ASCII decimal digits, at least one.
decimalG :: RegGrammatical Char p => p String String
decimalG = someP (oneOf ['0' .. '9'])

-- An optional minus, as whether a number is negative.
negativeG :: RegGrammatical Char p => p Bool Bool
negativeG = iso (\b -> if b then Just () else Nothing) isJust
  >~ optionalP (terminal "-")

-- Printing canonically, parsing leading zeros too, an improper iso.
naturalG :: RegGrammatical Char p => p Natural Natural
naturalG = iso show read >~ decimalG

-- Printing canonically, parsing leading zeros & -0 too, an improper iso.
integerG :: RegGrammatical Char p => p Integer Integer
integerG = iso
  (\n -> (n < 0, show (abs n)))
  (\(negative, digits) -> (if negative then negate else id) (read digits))
  >~ negativeG >*< decimalG

-- Integers in a range, failing to build out of it.
sizedG
  :: forall a p. (Integral a, Bits a, CtxGrammatical Char p) => p a a
sizedG = prism' toInteger toIntegralSized ?< integerG

{- Floating point numbers, @NaN@, or signed @Infinity@ or decimals with
an optional fraction & exponent, printing as `show` does & parsing as
`read` does, an improper iso, keeping the sign of zero. -}
floatingG
  :: (RealFloat a, Read a, Show a, RegGrammatical Char p) => p a a
floatingG = iso toFloating fromFloating >~
  terminal "NaN" >+< negativeG >*< (terminal "Infinity" >+< numberG)
  where
    numberG = decimalG
      >*< optionalP (terminal "." >* decimalG)
      >*< optionalP (oneOf "eE" >*< optionalP (oneOf "+-") >*< decimalG)
    toFloating x
      | isNaN x = Left ()
      | otherwise = Right
          ( x < 0 || isNegativeZero x
          , if isInfinite x then Left () else Right (split (show (abs x))) )
    fromFloating = \case
      Left () -> 0 / 0
      Right (negative, magnitude) -> (if negative then negate else id) $
        either (const (1 / 0)) (read . unsplit) magnitude
    split shown =
      let
        (whole, rest) = span isDigit shown
        (fraction, rest') = case rest of
          '.' : more -> let (ds, more') = span isDigit more in (Just ds, more')
          _ -> (Nothing, rest)
        exponent' = case rest' of
          e : more | e `elem` ("eE" :: String) -> case more of
            s : ds | s `elem` ("+-" :: String) -> Just (e, (Just s, ds))
            ds -> Just (e, (Nothing, ds))
          _ -> Nothing
      in
        (whole, (fraction, exponent'))
    unsplit (whole, (fraction, exponent')) = whole
      <> maybe "" ('.' :) fraction
      <> maybe "" (\(e, (s, ds)) -> e : maybe "" pure s <> ds) exponent'

instance CtxGrammar Char (RegEx Char)
instance Grammar Char (RegEx Char) where grammar = regexGrammar
instance CtxGrammar Char (Bnf (RegEx Char))
instance Grammar Char (Bnf (RegEx Char)) where grammar = regbnfGrammar
