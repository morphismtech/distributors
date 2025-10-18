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

module Text.Grammar.Distributor2
  ( -- * Context Free Grammar
    Grammar
  , Grammarr
  , Grammatical (..)
  , InvariantP (..)
  , Gram (..)
--   , gramGram
    -- * Regular Grammar
  , RegGrammar
  , Regular (..)
  , RegEx (..)
  , regexNorm
  , regexShow
  , regexRead
  , regexGram
    -- * Context Sensitive Grammar
  , CtxGrammar
  , CtxGrammarr
  , Contextual
  , Subtextual
    -- * Generators
  , genRead
  , genShow
  , genCtx
  , genRegEx
--   , genGram
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.PartialIso
import Control.Monad
import Data.Char
import Data.Coerce
import Data.Foldable
import Data.Function
import Data.Kind
import Data.Maybe hiding (mapMaybe)
import Data.Monoid
import Data.Profunctor
import Data.Profunctor.Distributor
import Data.Profunctor.Monadic
import Data.Set (Set, insert)
import Data.String
import GHC.Generics
import Witherable

-- Context Free Grammar --

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

To see an example of a `Grammar`, look at the source of `regexGram`.
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
  ( Regular p
  , Filtrator p
  ) => Grammatical p where

    {- | A nonterminal rule.
    prop> rule name p = ruleRec name (\_ -> p)
    -}
    rule :: String -> p a a -> p a a
    rule _ = id

    {- | A recursive, nonterminal rule. -}
    ruleRec :: String -> (p a a -> p a a) -> p a a
    ruleRec _ = fix

instance (Alternative f, Cons s s Char Char)
  => Grammatical (Printor s s f)
instance (Monad f, Alternative f, Filterable f, Cons s s Char Char)
  => Grammatical (Parsor s s f)
instance (Alternative f, Filterable f, Cons s s Char Char)
  => Grammatical (CtxPrintor s s f)

newtype InvariantP i j f a b = InvariantP {runInvariantP :: i -> f j}
instance Functor (InvariantP i j f a) where fmap _ = coerce
instance Contravariant (InvariantP i j f a) where contramap _ = coerce
instance Profunctor (InvariantP i j f) where dimap _ _ = coerce
instance Bifunctor (InvariantP i j f) where bimap _ _ = coerce

data Gram r = Gram
  { startGram :: r
  , rulesGram :: Set (String, r)
  } deriving Show

-- RegEx --

type RegGrammar a = forall p. Regular p => p a a

class
  ( Alternator p
  , Tokenized Char Char p
  ) => Regular p where

    {- | Only characters which are in the given `String`.-}
    inClass :: String -> p Char Char
    default inClass :: Filtrator p => String -> p Char Char
    inClass str = satisfy $ \ch -> elem ch str

    {- | Only characters which are not in the given `String`.-}
    notInClass :: String -> p Char Char
    default notInClass :: Filtrator p => String -> p Char Char
    notInClass str = satisfy $ \ch -> notElem ch str

    {- | Only characters which are in the given `GeneralCategory`.-}
    inCategory :: GeneralCategory -> p Char Char
    default inCategory :: Filtrator p => GeneralCategory -> p Char Char
    inCategory cat = satisfy $ \ch -> cat == generalCategory ch

    {- | Only characters which are not in the given `GeneralCategory`.-}
    notInCategory :: GeneralCategory -> p Char Char
    default notInCategory :: Filtrator p => GeneralCategory -> p Char Char
    notInCategory cat = satisfy $ \ch -> cat /= generalCategory ch

instance (Alternative f, Cons s s Char Char)
  => Regular (Printor s s f)
instance (Monad f, Alternative f, Filterable f, Cons s s Char Char)
  => Regular (Parsor s s f)
instance (Alternative f, Filterable f, Cons s s Char Char)
  => Regular (CtxPrintor s s f)

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

instance Applicative f => Applicative (InvariantP i RegEx f a) where
  pure _ = InvariantP (pure (pure (Terminal [])))
  InvariantP rex1 <*> InvariantP rex2 = InvariantP (liftA2 Sequence <$> rex1 <*> rex2)
instance Applicative f => Alternative (InvariantP i RegEx f a) where
  empty = InvariantP (pure (pure Fail))
  InvariantP rex1 <|> InvariantP rex2 = InvariantP (fmap regexNorm <$> (liftA2 Alternate <$> rex1 <*> rex2))
  many (InvariantP rex) = InvariantP (fmap (regexNorm . KleeneStar) <$> rex)
  some (InvariantP rex) = InvariantP (fmap (regexNorm . KleenePlus) <$> rex)
instance Applicative f => Distributor (InvariantP i RegEx f) where
  zeroP = InvariantP (pure (pure Fail))
  InvariantP rex1 >+< InvariantP rex2 = InvariantP (fmap regexNorm <$> (liftA2 Alternate <$> rex1 <*> rex2))
  manyP (InvariantP rex) = InvariantP (fmap (regexNorm . KleeneStar) <$> rex)
instance Choice (InvariantP i RegEx f) where
  left' = coerce
  right' = coerce
instance Cochoice (InvariantP i RegEx ((,) All)) where
  unleft = InvariantP . ((\(_,rex) -> (All False,rex)) .) . runInvariantP
  unright = InvariantP . ((\(_,rex) -> (All False,rex)) .) . runInvariantP
instance Applicative f => Alternator (InvariantP i RegEx f) where
  alternate = either coerce coerce
  someP (InvariantP rex) = InvariantP (fmap (regexNorm . KleenePlus) <$> rex)
instance Applicative f => IsString (InvariantP i RegEx f () ()) where
  fromString str = InvariantP (pure (pure (Terminal str)))
instance Applicative f => Tokenized Char Char (InvariantP i RegEx f) where
  anyToken = InvariantP (pure (pure AnyChar))
instance Applicative f => Regular (InvariantP i RegEx f) where
  inClass str = InvariantP (pure (pure (InClass str)))
  notInClass str = InvariantP (pure (pure (NotInClass str)))
  inCategory cat = InvariantP (pure (pure (InCategory cat)))
  notInCategory cat = InvariantP (pure (pure (NotInCategory cat)))

regexNorm :: RegEx -> RegEx
regexNorm rex = rex

regexShow :: RegEx -> String
regexShow rex = fromMaybe "\\q" (genShow regexGram rex)

regexRead :: String -> RegEx
regexRead str = fromMaybe Fail (genRead regexGram str)

{- | `regexGram` provides an important example of a `Grammar`.
Take a look at the source to see its definition.

>>> printGrammar regexGram
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
regexGram :: Grammar RegEx
regexGram = ruleRec "regex" $ \rex -> altG rex

altG :: Grammarr RegEx RegEx
altG rex = rule "alternate" $
  chainl1 _Alternate (sepBy (token '|')) (seqG rex)

anyG :: Grammar RegEx
anyG = rule "any" $ _AnyChar >?< tokens "."

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
  _LowercaseLetter >?< tokens "Ll"
  <|> _UppercaseLetter >?< tokens "Lu"
  <|> _TitlecaseLetter >?< tokens "Lt"
  <|> _ModifierLetter >?< tokens "Lm"
  <|> _OtherLetter >?< tokens "Lo"
  <|> _NonSpacingMark >?< tokens "Mn"
  <|> _SpacingCombiningMark >?< tokens "Mc"
  <|> _EnclosingMark >?< tokens "Me"
  <|> _DecimalNumber >?< tokens "Nd"
  <|> _LetterNumber >?< tokens "Nl"
  <|> _OtherNumber >?< tokens "No"
  <|> _ConnectorPunctuation >?< tokens "Pc"
  <|> _DashPunctuation >?< tokens "Pd"
  <|> _OpenPunctuation >?< tokens "Ps"
  <|> _ClosePunctuation >?< tokens "Pe"
  <|> _InitialQuote >?< tokens "Pi"
  <|> _FinalQuote >?< tokens "Pf"
  <|> _OtherPunctuation >?< tokens "Po"
  <|> _MathSymbol >?< tokens "Sm"
  <|> _CurrencySymbol >?< tokens "Sc"
  <|> _ModifierSymbol >?< tokens "Sk"
  <|> _OtherSymbol >?< tokens "So"
  <|> _Space >?< tokens "Zs"
  <|> _LineSeparator >?< tokens "Zl"
  <|> _ParagraphSeparator >?< tokens "Zp"
  <|> _Control >?< tokens "Cc"
  <|> _Format >?< tokens "Cf"
  <|> _Surrogate >?< tokens "Cs"
  <|> _PrivateUse >?< tokens "Co"
  <|> _NotAssigned >?< tokens "Cn"

categoryInG :: Grammar RegEx
categoryInG = rule "category-in" $
  _InCategory >?< tokens "\\p" >* parenCurlyG categoryG

categoryNotInG :: Grammar RegEx
categoryNotInG = rule "category-not-in" $
  _NotInCategory >?< tokens "\\P" >* parenCurlyG categoryG

charG :: Grammar Char
charG = rule "char" $ charLiteralG <|> charEscapedG

charEscapedG :: Grammar Char
charEscapedG = rule "char-escaped" $ token '\\' >* inClass charsReserved

charLiteralG :: Grammar Char
charLiteralG = rule "char-literal" $ notInClass charsReserved

charsReserved :: String
charsReserved = "$()*+.?[\\]^{|}"

classInG :: Grammar RegEx
classInG = rule "class-in" $
  _InClass >?< parenSquareG (manyP charG)

classNotInG :: Grammar RegEx
classNotInG = rule "class-not-in" $
  _NotInClass >?< parenSquareG (token '^' >* manyP charG)

exprG :: Grammarr RegEx RegEx
exprG rex = rule "expression" $
  terminalG
  <|> kleeneOptG rex
  <|> kleeneStarG rex
  <|> kleenePlusG rex
  <|> atomG rex

failG :: Grammar RegEx
failG = rule "fail" $ _Fail >?< tokens "\\q"

nonterminalG :: Grammar RegEx
nonterminalG = rule "nonterminal" $
  _NonTerminal >?< tokens "\\q" >* parenCurlyG (manyP charG)

parenG :: Grammarr a a
parenG rex = rule "parenthesized" $
  token '(' >* rex *< token ')'

parenCurlyG :: Grammarr a a
parenCurlyG rex = rule "parenthesized-curly" $
  token '{' >* rex *< token ')'

parenSquareG :: Grammarr a a
parenSquareG rex = rule "parenthesized-square" $
  token '[' >* rex *< token ']'

kleeneOptG :: Grammarr RegEx RegEx
kleeneOptG rex = rule "kleene-optional" $
  _KleeneOpt >?< atomG rex *< token '?'

kleeneStarG :: Grammarr RegEx RegEx
kleeneStarG rex = rule "kleene-star" $
  _KleeneStar >?< atomG rex *< token '*'

kleenePlusG :: Grammarr RegEx RegEx
kleenePlusG rex = rule "kleene-plus" $
  _KleenePlus >?< atomG rex *< token '+'

seqG :: Grammarr RegEx RegEx
seqG rex = rule "sequence" $
  chainl _Sequence (_Terminal . _Empty) noSep (exprG rex)

terminalG :: Grammar RegEx
terminalG = rule "terminal" $
  _Terminal >?< someP charG

-- Context Sensitive Grammar --

type CtxGrammar a = forall p m.
  (Contextual p, Subtextual m) => p String String m a a

type CtxGrammarr a b = forall p m.
  (Contextual p, Subtextual m) => p String String m a a -> p String String m b b

type Contextual :: (Type -> Type -> (Type -> Type) -> Type -> Type -> Type) -> Constraint
type Contextual p =
  ( Polyadic p
  , Tetradic p
  , forall m. Subtextual m => Grammatical (p String String m :: Type -> Type -> Type)
  )

type Subtextual m =
  ( Alternative m
  , Filterable m
  , MonadPlus m
  )

-- Generators --

genRead :: Subtextual m => CtxGrammar a -> String -> m a
genRead grammar = mapMaybe nonempty . runParsor grammar
  where
    nonempty = \case
      (a,"") -> Just a
      _ -> Nothing

genShow :: Subtextual m => CtxGrammar a -> a -> m String
genShow grammar = fmap (($ "") . snd) . runCtxPrintor grammar

genCtx :: Subtextual m => CtxGrammar a -> a -> m a
genCtx grammar = fmap fst . runCtxPrintor grammar

genRegEx :: RegGrammar a -> RegEx
genRegEx = runIdentity . ($ ()) . runInvariantP
