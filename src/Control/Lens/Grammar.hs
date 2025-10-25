module Control.Lens.Grammar
  ( -- *
    RegGrammar
  , Grammar
  , CtxGrammar
  , opticGrammar
  , grammarOptic
  , RegGrammarr
  , Grammarr
  , CtxGrammarr
  , opticGrammarr
  , grammarrOptic
  , genShowS
  , genReadS
  , Regular
  , Grammatical
  , Contextual
  , RegEx (..)
  , regexGrammar
  , normRegEx
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.PartialIso
import Control.Lens.Grammar.BackusNaur
import Control.Lens.Grammar.Kleene
import Control.Lens.Grammar.Token
import Control.Lens.Grammar.Stream
import Control.Lens.Grammar.Symbol
import Control.Monad
import qualified Data.Foldable as F
import Data.Profunctor.Distributor
import Data.Profunctor.Filtrator
import Data.Profunctor.Monadic
import Data.Profunctor.Monoidal
import Data.Profunctor.Grammar
import GHC.Exts
import Witherable

type RegGrammar c a = forall p. Regular c p => p a a
type Grammar c a = forall p. Grammatical c p => p a a
type CtxGrammar s a = forall p m. Contextual s m p => p s s m a a

opticGrammar :: Monoidal p => Optic' p Identity a () -> p a a
opticGrammar = ($ oneP) . opticGrammarr

grammarOptic :: Monoidal p => p a a -> Optic' p Identity a ()
grammarOptic = grammarrOptic . (*<)

type RegGrammarr c a b = forall p. Regular c p => p a a -> p b b
type Grammarr c a b = forall p. Grammatical c p => p a a -> p b b
type CtxGrammarr s a b = forall p m. Contextual s m p => p s s m a a -> p s s m b b

opticGrammarr :: Profunctor p => Optic' p Identity b a -> p a a -> p b b
opticGrammarr = dimap (rmap Identity) (rmap runIdentity)

grammarrOptic :: Profunctor p => (p a a -> p b b) -> Optic' p Identity b a
grammarrOptic = dimap (rmap runIdentity) (rmap Identity)

genShowS
  :: (Filterable m, MonadPlus m)
  => CtxGrammar String a -> a -> m ShowS
genShowS = runPrintor . toPrintor

genReadS :: CtxGrammar String a -> ReadS a
genReadS = runParsor

type Regular c p =
  ( Terminator c p
  , Tokenizor c p
  , Alternator p
  )

type Grammatical c p =
  ( Regular c p
  , Filtrator p
  , forall x. BackusNaurForm (p x x)
  )

type Contextual s m p =
  ( Grammatical (Item s) (p s s m)
  , Monadic (p s s)
  , Subtextual s m
  )

data RegEx a
  = Terminal [a]
  | Sequence (RegEx a) (RegEx a)
  | Fail
  | Alternate (RegEx a) (RegEx a)
  | KleeneOpt (RegEx a)
  | KleeneStar (RegEx a)
  | KleenePlus (RegEx a)
  | AnyToken
  | OneOf [a]
  | NotOneOf [a]
  | AsIn (Categorize a)
  | NotAsIn (Categorize a)
  | NonTerminal String

normRegEx :: Categorized a => RegEx a -> RegEx a
normRegEx = \case
  Sequence rex1 rex2 -> normRegEx rex1 <> normRegEx rex2
  Alternate rex1 rex2 -> normRegEx rex1 `altK` normRegEx rex2
  KleeneOpt rex -> optK (normRegEx rex)
  KleeneStar rex -> starK (normRegEx rex)
  KleenePlus rex -> plusK (normRegEx rex)
  OneOf [a] -> token a
  rex -> rex

deriving stock instance Categorized a => Eq (RegEx a)
deriving stock instance
  (Categorized a, Ord a, Ord (Categorize a)) => Ord (RegEx a)
deriving stock instance
  (Categorized a, Read a, Read (Categorize a)) => Read (RegEx a)
deriving stock instance
  (Categorized a, Show a, Show (Categorize a)) => Show (RegEx a)
instance TerminalSymbol (RegEx a) where
  type Alphabet (RegEx a) = a
  terminal = Terminal . F.toList
instance Monoid a => TerminalSymbol (a, RegEx a) where
  type Alphabet (a, RegEx a) = a
  terminal = pure . terminal
instance Categorized a => Tokenized (RegEx a) where
  type Token (RegEx a) = a
  anyToken = AnyToken
  token a = Terminal [a]
  oneOf = OneOf . F.toList
  notOneOf = NotOneOf . F.toList
  asIn = AsIn
  notAsIn = NotAsIn
instance Categorized a => Semigroup (RegEx a) where
  Terminal [] <> rex = rex
  rex <> Terminal [] = rex
  Fail <> _ = empK
  _ <> Fail = empK
  Terminal str0 <> Terminal str1 = Terminal (str0 <> str1)
  KleeneStar rex0 <> rex1
    | rex0 == rex1 = plusK rex0
  rex0 <> KleeneStar rex1
    | rex0 == rex1 = plusK rex1
  rex0 <> rex1 = Sequence rex0 rex1
instance Categorized a => Monoid (RegEx a) where
  mempty = Terminal []
instance Categorized a => KleeneStarAlgebra (RegEx a) where
  empK = Fail
  optK Fail = mempty
  optK (Terminal []) = mempty
  optK (KleenePlus rex) = starK rex
  optK rex = KleeneOpt rex
  starK Fail = mempty
  starK (Terminal []) = mempty
  starK rex = KleeneStar rex
  plusK Fail = empK
  plusK (Terminal []) = mempty
  plusK rex = KleenePlus rex
  KleenePlus rex `altK` Terminal [] = starK rex
  Terminal [] `altK` KleenePlus rex = starK rex
  rex `altK` Terminal [] = optK rex
  Terminal [] `altK` rex = optK rex
  rex `altK` Fail = rex
  Fail `altK` rex = rex
  rex0 `altK` rex1 | rex0 == rex1 = rex0
  rex0 `altK` rex1 = Alternate rex0 rex1
instance NonTerminalSymbol (RegEx a) where
  nonTerminal = NonTerminal

instance Applicative f
  => TerminalSymbol (Grammor s (RegEx a) f () ()) where
  type Alphabet (Grammor s (RegEx a) f () ()) = a
  terminal = Grammor . pure . pure . terminal

makeNestedPrisms ''RegEx
makeNestedPrisms ''GeneralCategory

regexGrammar :: Grammar Char (RegEx Char)
regexGrammar = ruleRec "regex" $ \rex -> altG rex
  where

    altG rex = rule "alternate" $
      chain1 Left _Alternate (sepBy (terminal "|")) (seqG rex)

    anyG = rule "any" $ _AnyToken >?< terminal "."

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

    categoryG = rule "category" $
      _LowercaseLetter >?< terminal "Ll"
      <|> _UppercaseLetter >?< terminal "Lu"
      <|> _TitlecaseLetter >?< terminal "Lt"
      <|> _ModifierLetter >?< terminal "Lm"
      <|> _OtherLetter >?< terminal "Lo"
      <|> _NonSpacingMark >?< terminal "Mn"
      <|> _SpacingCombiningMark >?< terminal "Mc"
      <|> _EnclosingMark >?< terminal "Me"
      <|> _DecimalNumber >?< terminal "Nd"
      <|> _LetterNumber >?< terminal "Nl"
      <|> _OtherNumber >?< terminal "No"
      <|> _ConnectorPunctuation >?< terminal "Pc"
      <|> _DashPunctuation >?< terminal "Pd"
      <|> _OpenPunctuation >?< terminal "Ps"
      <|> _ClosePunctuation >?< terminal "Pe"
      <|> _InitialQuote >?< terminal "Pi"
      <|> _FinalQuote >?< terminal "Pf"
      <|> _OtherPunctuation >?< terminal "Po"
      <|> _MathSymbol >?< terminal "Sm"
      <|> _CurrencySymbol >?< terminal "Sc"
      <|> _ModifierSymbol >?< terminal "Sk"
      <|> _OtherSymbol >?< terminal "So"
      <|> _Space >?< terminal "Zs"
      <|> _LineSeparator >?< terminal "Zl"
      <|> _ParagraphSeparator >?< terminal "Zp"
      <|> _Control >?< terminal "Cc"
      <|> _Format >?< terminal "Cf"
      <|> _Surrogate >?< terminal "Cs"
      <|> _PrivateUse >?< terminal "Co"
      <|> _NotAssigned >?< terminal "Cn"

    categoryInG = rule "category-in" $
      _AsIn >?< terminal "\\p{" >* categoryG *< terminal "}"

    categoryNotInG = rule "category-not-in" $
      _NotAsIn >?< terminal "\\P{" >* categoryG *< terminal "}"

    charG = rule "char" $ charLiteralG <|> charEscapedG

    charEscapedG = rule "char-escaped" $ terminal "\\" >* oneOf charsReserved

    charLiteralG = rule "char-literal" $ notOneOf charsReserved

    charsReserved :: String
    charsReserved = "$()*+.?[\\]^{|}"

    classInG = rule "class-in" $
      _OneOf >?< terminal "[" >* manyP charG *< terminal "]"

    classNotInG = rule "class-not-in" $
      _NotOneOf >?< terminal "[^" >* manyP charG *< terminal "]"

    exprG rex = rule "expression" $
      terminalG
      <|> kleeneOptG rex
      <|> kleeneStarG rex
      <|> kleenePlusG rex
      <|> atomG rex

    failG = rule "fail" $ _Fail >?< terminal "\\q"

    nonterminalG = rule "nonterminal" $
      _NonTerminal >?< terminal "\\q{" >* manyP charG *< terminal "}"

    parenG :: Grammarr Char x x
    parenG ex = rule "parenthesized" $
      terminal "(" >* ex *< terminal ")"

    kleeneOptG rex = rule "kleene-optional" $
      _KleeneOpt >?< atomG rex *< terminal "?"

    kleeneStarG rex = rule "kleene-star" $
      _KleeneStar >?< atomG rex *< terminal "*"

    kleenePlusG rex = rule "kleene-plus" $
      _KleenePlus >?< atomG rex *< terminal "+"

    seqG rex = rule "sequence" $
      chain Left _Sequence (_Terminal . _Empty) noSep (exprG rex)

    terminalG = rule "terminal" $
      _Terminal >?< someP charG
