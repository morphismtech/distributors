module Control.Lens.Grammar
  ( -- * RegEx
    RegExStr (..)
  , EBNF (..)
  , RegGrammar
  , RegGrammarr
  , bnfGrammarr
  , genRegExStr
  , printRegEx
  , genShowS
  , genReadS
    -- * Grammar
  , Grammar
  , genEBNF
  , printEBNF
  , regexGrammar
  , ebnfGrammar
  , Grammarr
  , CtxGrammar
  , CtxGrammarr
    -- * Optics
  , prismGrammar
  , coPrismGrammar
  , grammarrOptic
  , grammarOptic
    -- * Constraints
  , Regular
  , Grammatical
  , Contextual
    -- * Re-exports
  , oneP, (>*), (*<), (>*<), replicateP
  , empty, (<|>), manyP, someP, optionalP
  , module Control.Lens.Grammar.BackusNaur
  , module Control.Lens.Grammar.Kleene
  , module Control.Lens.Grammar.Token
  , module Control.Lens.Grammar.Stream
  , module Control.Lens.Grammar.Symbol
  , module Control.Lens.PartialIso
  , module Data.Profunctor.Grammar
  ) where

import Control.Applicative
import Control.Comonad
import Control.Lens
import Control.Lens.PartialIso
import Control.Lens.Grammar.BackusNaur
import Control.Lens.Grammar.Kleene
import Control.Lens.Grammar.Token
import Control.Lens.Grammar.Stream
import Control.Lens.Grammar.Symbol
import Control.Monad
-- import Control.Monad.Except
import Data.Maybe hiding (mapMaybe)
import Data.Monoid
import Data.Profunctor
import Data.Profunctor.Distributor
import Data.Profunctor.Filtrator
import Data.Profunctor.Monadic
import Data.Profunctor.Monoidal
import Data.Profunctor.Grammar
import Data.String
import GHC.Exts
import Prelude hiding (filter)
import Witherable

makeNestedPrisms ''RegEx
makeNestedPrisms ''GeneralCategory

type RegGrammar token a = forall p. Regular token p => p a a
type Grammar token a = forall p. Grammatical token p => p a a
type CtxGrammar token a = forall p m. Contextual token m p => p m a a

type RegGrammarr token a b =
  forall p. Regular token p => p a a -> p b b
type Grammarr token a b =
  forall p. Grammatical token p => p a a -> p b b
type CtxGrammarr token a b =
  forall p m. Contextual token m p => p m a a -> p m b b

type Regular token p =
  ( Terminator token p
  , Tokenizor token p
  , Alternator p
  )
type Grammatical token p =
  ( Regular token p
  , Filtrator p
  , forall x. BackusNaurForm (p x x)
  )
type Contextual token m p =
  ( Grammatical token (p m)
  , Monadic m p
  , Filterable m
  , Alternative m
  , Monad m
  )

prismGrammar :: (Monoidal p, Choice p) => Prism' a () -> p a a
prismGrammar = (>? oneP)

coPrismGrammar :: (Monoidal p, Cochoice p) => Prism' () a -> p a a
coPrismGrammar = (?< oneP)

grammarOptic
  :: (Monoidal p, Comonad f, Applicative f)
  => p a a -> Optic' p f a ()
grammarOptic = grammarrOptic . (*<)

grammarrOptic
  :: (Profunctor p, Comonad f, Applicative f)
  => (p a a -> p b b) -> Optic' p f b a
grammarrOptic = dimap (rmap extract) (rmap pure)

genShowS
  :: (Filterable m, Alternative m, Monad m)
  => CtxGrammar Char a -> a -> m ShowS
genShowS = evalPrintor

genReadS :: CtxGrammar Char a -> ReadS a
genReadS = runParsor

genRegExStr :: RegGrammar Char a -> RegExStr
genRegExStr = evalGrammor @() @Identity

genEBNF :: Grammar Char a -> EBNF
genEBNF = evalGrammor @() @((,) All)

regexGrammar :: Grammar Char RegExStr
regexGrammar = dimap runRegExStr RegExStr $ ruleRec "regex" altG
  where
    altG rex = rule "alternate" $
      chain1 Left _Alternate (sepBy (terminal "|")) (seqG rex)
    seqG rex = rule "sequence" $
      chain Left _Sequence (_Terminal . _Empty) noSep (exprG rex)
    exprG rex = rule "expression" $ choiceP
      [ _Terminal >? someP charG
      , _KleeneOpt >? atomG rex *< terminal "?"
      , _KleeneStar >? atomG rex *< terminal "*"
      , _KleenePlus >? atomG rex *< terminal "+"
      , atomG rex
      ]
    atomG rex = rule "atom" $ choiceP
      [ nonterminalG
      , _Terminal >? charG >:< pure ""
      , _AnyToken >? terminal "."
      , _OneOf >? terminal "[" >* someP charG *< terminal "]"
      , _NotOneOf >? terminal "[^" >* someP charG *< terminal "]"
      , _AsIn >? terminal "\\p{" >* categoryG *< terminal "}"
      , _NotAsIn >? terminal "\\P{" >* categoryG *< terminal "}"
      , terminal "(" >* rex *< terminal ")"
      ]
    charG = rule "char" $ escapes
      [ ("$()*+.?[\\]^{|}", (terminal "\\" >*))
      , ("\n", \_ -> (terminal "\\n" <|> terminal "\n") >* pure '\n')
      , ("\t", \_ -> (terminal "\\t" <|> terminal "\t") >* pure '\t')
      ]
    categoryG = rule "category" $ choiceP
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
    nonterminalG = rule "nonterminal" $ terminal "\\q" >* choiceP
      [ _NonTerminal >? terminal "{" >* manyP charG *< terminal "}"
      , prismGrammar _Fail
      ]

bnfGrammarr :: Ord rule => RegGrammarr Char rule (BNF rule)
bnfGrammarr p = dimap hither thither $ startG  >*< rulesG
  where
    hither (BNF start rules) = (start, toList rules)
    thither (start, rules) = BNF start (fromList rules)
    startG = terminal "start" >* ruleG
    rulesG = manyP (terminal ['\n'] >* nameG >*< ruleG)
    ruleG = terminal " = " >* p
    nameG = manyP (escape "\\= " (terminal "\\" >*))

ebnfGrammar :: Grammar Char EBNF
ebnfGrammar = dimap runEBNF EBNF (bnfGrammarr regexGrammar)

newtype RegExStr = RegExStr {runRegExStr :: RegEx Char}
  deriving newtype
    ( Eq, Ord
    , Semigroup, Monoid, KleeneStarAlgebra
    , Tokenized, TerminalSymbol, NonTerminalSymbol
    )
newtype EBNF = EBNF {runEBNF :: BNF RegExStr}
  deriving newtype
    ( Eq, Ord
    , Semigroup, Monoid, KleeneStarAlgebra
    , Tokenized, TerminalSymbol, NonTerminalSymbol
    , BackusNaurForm
    )

printRegEx :: RegGrammar Char a -> IO ()
printRegEx = streamLine . genRegExStr

printEBNF :: Grammar Char a -> IO ()
printEBNF = streamLine . genEBNF

instance IsList RegExStr where
  type Item RegExStr = Char
  fromList
    = fromMaybe (RegExStr Fail)
    . listToMaybe
    . mapMaybe (\(rex, remaining) -> if remaining == "" then Just rex else Nothing)
    . genReadS regexGrammar
  toList
    = maybe "\\q" ($ "")
    . genShowS regexGrammar
instance IsString RegExStr where
  fromString = fromList
instance Show RegExStr where
  showsPrec precision = showsPrec precision . toList
instance Read RegExStr where
  readsPrec _ str = [(fromList str, "")]
instance IsList EBNF where
  type Item EBNF = Char
  fromList
    = fromMaybe (EBNF (BNF (RegExStr Fail) mempty))
    . listToMaybe
    . mapMaybe (\(ebnf, remaining) -> if remaining == "" then Just ebnf else Nothing)
    . genReadS ebnfGrammar
  toList
    = maybe "{start} = \\q" ($ "")
    . genShowS ebnfGrammar
instance IsString EBNF where
  fromString = fromList
instance Show EBNF where
  showsPrec precision = showsPrec precision . toList
instance Read EBNF where
  readsPrec _ str = [(fromList str, "")]
