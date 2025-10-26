module Control.Lens.Grammar
  ( -- * RegEx
    RegExStr
  , RegGrammar
  , genRegEx
  , genShowS
  , genReadS
    -- * Grammar
  , Grammar
  , genGram
  , regexString
    -- * CtxGrammar
  , CtxGrammar
    -- * Optics
  , RegGrammarr
  , Grammarr
  , CtxGrammarr
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
import Control.Lens
import Control.Lens.PartialIso
import Control.Lens.Grammar.BackusNaur
import Control.Lens.Grammar.Kleene
import Control.Lens.Grammar.Token
import Control.Lens.Grammar.Stream
import Control.Lens.Grammar.Symbol
import Control.Monad
import Data.Maybe
import Data.Monoid
import Data.Profunctor.Distributor
import Data.Profunctor.Filtrator
import Data.Profunctor.Monadic
import Data.Profunctor.Monoidal
import Data.Profunctor.Grammar
import Data.String
import GHC.Exts
import Prelude hiding (filter)
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

makeNestedPrisms ''RegEx
makeNestedPrisms ''GeneralCategory

regexString :: Grammar Char RegExStr
regexString = dimap runRegExStr RegExStr . ruleRec "regex" $ \rex -> altG rex
  where
    altG rex = rule "alternate" $
      chain1 Left _Alternate (sepBy (terminal "|")) (seqG rex)
    anyG = rule "any" $ _AnyToken >?< terminal "."
    atomG rex = rule "atom" $ choiceP
      [ nonterminalG
      , failG
      , classInG
      , classNotInG
      , categoryInG
      , categoryNotInG
      , _Terminal >?< charG >:< pure ""
      , anyG
      , parenG rex
      ]
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
    charG = rule "char" $ charLiteralG <|> charEscapedG
    charEscapedG = rule "char-escaped" $
      terminal "\\" >* oneOf charsReserved
    charLiteralG = rule "char-literal" $ notOneOf charsReserved
    charsReserved :: String
    charsReserved = "$()*+.?[\\]^{|}"
    classInG = rule "class-in" $
      _OneOf >?< terminal "[" >* manyP charG *< terminal "]"
    classNotInG = rule "class-not-in" $
      _NotOneOf >?< terminal "[^" >* manyP charG *< terminal "]"
    exprG rex = rule "expression" $ choiceP
      [ terminalG
      , kleeneOptG rex
      , kleeneStarG rex
      , kleenePlusG rex
      , atomG rex
      ]
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
    terminalG = rule "terminal" $ _Terminal >?< someP charG

newtype RegExStr = RegExStr {runRegExStr :: RegEx Char}

instance IsList RegExStr where
  type Item RegExStr = Char
  fromList
    = maybe (RegExStr Fail) fst
    . listToMaybe
    . filter (\(_, remaining) -> remaining == "")
    . genReadS regexString
  toList
    = maybe "\\q" ($ "")
    . genShowS regexString

instance IsString RegExStr where
  fromString = fromList

instance Show RegExStr where
  showsPrec precision = showsPrec precision . toList

instance Read RegExStr where
  readsPrec _ str = [(fromList str, "")]
