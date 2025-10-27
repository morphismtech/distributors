module Control.Lens.Grammar
  ( -- * RegEx
    RegExStr
  , EBNF
  , RegGrammar
  , RegGrammarr
  , bnfGrammarr
  , genRegEx
  , printRegEx
  , genShowS
  , genReadS
    -- * Grammar
  , Grammar
  , genGram
  , printEBNF
  , regexGrammar
  , ebnfGrammar
  , Grammarr
  , CtxGrammar
  , CtxGrammarr
    -- * Optics
  , opticGrammarr
  , grammarrOptic
  , opticGrammar
  , grammarOptic
    -- * Constraints
  , Regular
  , Grammatical
  , Contextual
    -- * Re-exports
  , module Control.Lens.Grammar.BackusNaur
  , module Control.Lens.Grammar.Kleene
  , module Control.Lens.Grammar.Token
  , module Control.Lens.Grammar.Stream
  , module Control.Lens.Grammar.Symbol
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

type RegGrammar c a = forall p. Regular c p => p a a
type Grammar c a = forall p. Grammatical c p => p a a
type CtxGrammar s a = forall p m. Contextual s m p => p s s m a a

opticGrammar :: Monoidal p => Optic' p Identity a () -> p a a
opticGrammar = ($ oneP) . opticGrammarr

grammarOptic
  :: (Monoidal p, Comonad f, Applicative f)
  => p a a -> Optic' p f a ()
grammarOptic = grammarrOptic . (*<)

type RegGrammarr c a b = forall p.
  Regular c p => p a a -> p b b
type Grammarr c a b = forall p.
  Grammatical c p => p a a -> p b b
type CtxGrammarr s a b = forall p m.
  Contextual s m p => p s s m a a -> p s s m b b

opticGrammarr :: Profunctor p => Optic' p Identity b a -> p a a -> p b b
opticGrammarr = dimap (rmap Identity) (rmap runIdentity)

grammarrOptic
  :: (Profunctor p, Comonad f, Applicative f)
  => (p a a -> p b b) -> Optic' p f b a
grammarrOptic = dimap (rmap extract) (rmap pure)

genShowS
  :: (Filterable m, MonadPlus m)
  => CtxGrammar String a -> a -> m ShowS
genShowS = evalPrintor

genReadS :: CtxGrammar String a -> ReadS a
genReadS = runParsor

genRegEx :: Categorized token => RegGrammar token a -> RegEx token
genRegEx = evalGrammor @() @Identity

genGram
  :: (Categorized token, Ord token, Ord (Categorize token))
  => Grammar token a -> Gram (RegEx token)
genGram = evalGrammor @() @((,) All)

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
  , Categorized (Item s)
  , IsStream s
  , Filterable m
  , MonadPlus m
  )

regexGrammar :: Grammar Char (RegEx Char)
regexGrammar = ruleRec "regex" altG
  where
    altG rex = rule "alternate" $
      chain1 Left _Alternate (sepBy (terminal "|")) (seqG rex)
    seqG rex = rule "sequence" $
      chain Left _Sequence (_Terminal . _Empty) noSep (exprG rex)
    exprG rex = rule "expression" $ choiceP
      [ _Terminal >?< someP charG
      , _KleeneOpt >?< atomG rex *< terminal "?"
      , _KleeneStar >?< atomG rex *< terminal "*"
      , _KleenePlus >?< atomG rex *< terminal "+"
      , atomG rex
      ]
    atomG rex = rule "atom" $ choiceP
      [ nonterminalG
      , classInG
      , classNotInG
      , categoryInG
      , categoryNotInG
      , _Terminal >?< charG >:< pure ""
      , anyG
      , terminal "(" >* rex *< terminal ")"
      ]
    anyG = rule "any" $ _AnyToken >?< terminal "."
    categoryG = rule "category" $ choiceP
      [ _LowercaseLetter >?< terminal "Ll"
      , _UppercaseLetter >?< terminal "Lu"
      , _TitlecaseLetter >?< terminal "Lt"
      , _ModifierLetter >?< terminal "Lm"
      , _OtherLetter >?< terminal "Lo"
      , _NonSpacingMark >?< terminal "Mn"
      , _SpacingCombiningMark >?< terminal "Mc"
      , _EnclosingMark >?< terminal "Me"
      , _DecimalNumber >?< terminal "Nd"
      , _LetterNumber >?< terminal "Nl"
      , _OtherNumber >?< terminal "No"
      , _ConnectorPunctuation >?< terminal "Pc"
      , _DashPunctuation >?< terminal "Pd"
      , _OpenPunctuation >?< terminal "Ps"
      , _ClosePunctuation >?< terminal "Pe"
      , _InitialQuote >?< terminal "Pi"
      , _FinalQuote >?< terminal "Pf"
      , _OtherPunctuation >?< terminal "Po"
      , _MathSymbol >?< terminal "Sm"
      , _CurrencySymbol >?< terminal "Sc"
      , _ModifierSymbol >?< terminal "Sk"
      , _OtherSymbol >?< terminal "So"
      , _Space >?< terminal "Zs"
      , _LineSeparator >?< terminal "Zl"
      , _ParagraphSeparator >?< terminal "Zp"
      , _Control >?< terminal "Cc"
      , _Format >?< terminal "Cf"
      , _Surrogate >?< terminal "Cs"
      , _PrivateUse >?< terminal "Co"
      , _NotAssigned >?< terminal "Cn"
      ]
    categoryInG = rule "category-in" $
      _AsIn >?< terminal "\\p{" >* categoryG *< terminal "}"
    categoryNotInG = rule "category-not-in" $
      _NotAsIn >?< terminal "\\P{" >* categoryG *< terminal "}"
    charG = rule "char" $ escaped (terminal "\\" >*) "$()*+.?[\\]^{|}"
    classInG = rule "class-in" $
      _OneOf >?< terminal "[" >* manyP charG *< terminal "]"
    classNotInG = rule "class-not-in" $
      _NotOneOf >?< terminal "[^" >* manyP charG *< terminal "]"
    nonterminalG = rule "nonterminal" $ terminal "\\q" >*
      (_NonTerminal >?< terminal "{" >* manyP charG *< terminal "}" <|> _Fail >?< oneP)

bnfGrammarr :: Ord rule => RegGrammarr Char rule (Gram rule)
bnfGrammarr p = dimap hither thither $ startG  >*< rulesG
  where
    hither (Gram start rules) = (start, toList rules)
    thither (start, rules) = Gram start (fromList rules)
    ruleG = terminal " = " >* p
    startG = terminal "start" >* ruleG
    rulesG = manyP (terminal "\n" >* manyP (escaped (terminal "\\" >*) "\\=") >*< ruleG)

ebnfGrammar :: Grammar Char (Gram (RegEx Char))
ebnfGrammar = bnfGrammarr regexGrammar

newtype RegExStr = RegExStr {runRegExStr :: RegEx Char}
  deriving newtype (Eq, Ord)
newtype EBNF = EBNF {runEBNF :: Gram RegExStr}
  deriving newtype (Eq, Ord)

printRegEx :: RegGrammar Char a -> IO ()
printRegEx = putStrLn . toList . RegExStr . genRegEx @Char

printEBNF :: Grammar Char a -> IO ()
printEBNF = putStrLn . toList . EBNF . liftGram1 RegExStr . genGram @Char

instance IsList RegExStr where
  type Item RegExStr = Char
  fromList
    = fromMaybe (RegExStr Fail)
    . listToMaybe
    . mapMaybe (\(rex, remaining) -> if remaining == "" then Just rex else Nothing)
    . genReadS (dimap runRegExStr RegExStr regexGrammar)
  toList
    = maybe "\\q" ($ "")
    . genShowS (dimap runRegExStr RegExStr regexGrammar)
instance IsString RegExStr where
  fromString = fromList
instance Show RegExStr where
  showsPrec precision = showsPrec precision . toList
instance Read RegExStr where
  readsPrec _ str = [(fromList str, "")]
instance IsList EBNF where
  type Item EBNF = Char
  fromList
    = fromMaybe (EBNF (Gram (RegExStr Fail) mempty))
    . listToMaybe
    . mapMaybe (\(ebnf, remaining) -> if remaining == "" then Just ebnf else Nothing)
    . fmap (first' (EBNF . liftGram1 RegExStr))
    . genReadS ebnfGrammar
  toList
    = maybe "{start} = \\q" ($ "")
    . genShowS ebnfGrammar
    . liftGram1 runRegExStr
    . runEBNF
instance IsString EBNF where
  fromString = fromList
instance Show EBNF where
  showsPrec precision = showsPrec precision . toList
instance Read EBNF where
  readsPrec _ str = [(fromList str, "")]
