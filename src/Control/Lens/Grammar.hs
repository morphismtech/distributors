module Control.Lens.Grammar
  ( -- * RegEx
    RegString (..)
  , RegBnfString (..)
  , RegGrammar
  , RegGrammarr
  , ebnfGrammar
  , Grammar
  , Grammarr
  , regexGrammar
  , CtxGrammar
  , CtxGrammarr
  , Tokenizor
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.PartialIso
import Control.Lens.Grammar.BackusNaur
import Control.Lens.Grammar.Boole
import Control.Lens.Grammar.Kleene
import Control.Lens.Grammar.Token
import Control.Lens.Grammar.Symbol
import Control.Monad
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

makeNestedPrisms ''Bnf
makeNestedPrisms ''RegEx
makeNestedPrisms ''RegExam
makeNestedPrisms ''CategoryTest
makeNestedPrisms ''GeneralCategory

type RegGrammar token a = forall p.
  ( Tokenizor token p
  , Alternator p
  ) => p a a
type Grammar token a = forall p.
  ( Tokenizor token p
  , forall x. BackusNaurForm (p x x)
  , Alternator p
  ) => p a a
type CtxGrammar token a = forall p m.
  ( Tokenizor token (p m)
  , forall x. BackusNaurForm (p m x x)
  , Alternator (p m)
  , Filtrator (p m)
  , Monadic m p
  , Alternative m
  , Filterable m
  , Monad m
  ) => p m a a

type RegGrammarr token a b = forall p.
  ( Tokenizor token p
  , Alternator p
  ) => p a a -> p b b
type Grammarr token a b = forall p.
  ( Tokenizor token p
  , forall x. BackusNaurForm (p x x)
  , Alternator p
  ) => p a a -> p b b
type CtxGrammarr token a b = forall p m.
  ( Tokenizor token (p m)
  , forall x. BackusNaurForm (p m x x)
  , Alternator (p m)
  , Filtrator (p m)
  , Monadic m p
  , Alternative m
  , Filterable m
  , Monad m
  ) => p m a a -> p m b b

type Tokenizor token p =
  ( forall x y. (x ~ (), y ~ ()) => TerminalSymbol token (p x y)
  , forall x y. (x ~ token, y ~ token) => TokenAlgebra token (p x y)
  ) :: Constraint

regexGrammar :: Grammar Char (RegEx Char)
regexGrammar = ruleRec "regex" altG

ebnfGrammar :: Grammar Char (Bnf (RegEx Char))
ebnfGrammar = rule "ebnf" $ _Bnf >~
  terminal "start = " >* regexGrammar
    >*< several noSep (terminal "\n" >* ruleG)

altG :: Grammarr Char (RegEx Char) (RegEx Char)
altG rex = rule "alternate" $
  chain1 Left (_RegExam . _Alternate) (sepBy (terminal "|")) (seqG rex)

seqG :: Grammarr Char (RegEx Char) (RegEx Char)
seqG rex = rule "sequence" $ choiceP
  [ _Terminal >? manyP charG
  , chain Left _Sequence (_Terminal . _Empty) noSep (exprG rex)
  ]

exprG :: Grammarr Char (RegEx Char) (RegEx Char)
exprG rex = rule "expression" $ choiceP
  [ _KleeneOpt >? atomG rex *< terminal "?"
  , _KleeneStar >? atomG rex *< terminal "*"
  , _KleenePlus >? atomG rex *< terminal "+"
  , atomG rex
  ]

anyG :: Grammar Char ()
anyG = rule "any-token" $ choiceP $ map terminal
  [".", "[^]", "\\P{}", "[^\\P{}]"]

atomG :: Grammarr Char (RegEx Char) (RegEx Char)
atomG rex = rule "atom" $ choiceP
  [ _NonTerminal >? terminal "\\q{" >* manyP charG *< terminal "}"
  , _Terminal >? charG >:< asEmpty
  , _RegExam . _Fail >? failG
  , _RegExam . _Pass >? anyG
  , _RegExam . _OneOf >?
      terminal "[" >* several1 noSep charG *< terminal "]"
  , _RegExam . _NotOneOf >?
      terminal "[^" >* several1 noSep charG
        >*< (catTestG <|> pure (NotAsIn Set.empty))
        *< terminal "]"
  , _RegExam . _NotOneOf >? pure Set.empty >*< catTestG
  , terminal "(" >* rex *< terminal ")"
  ]

catTestG :: Grammar Char (CategoryTest Char)
catTestG = rule "category-test" $ choiceP
  [ _AsIn >? terminal "\\p{" >* categoryG *< terminal "}"
  , _NotAsIn >? terminal "\\P{" >*
      several1 (sepBy (terminal "|")) categoryG
        *< terminal "}"
  ]

categoryG :: Grammar Char GeneralCategory
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

charG :: Grammar Char Char
charG = rule "char" $
  tokenClass (notOneOf charsReserved >&&< notAsIn Control)
  <|> terminal "\\" >* charEscapedG

charEscapedG :: Grammar Char Char
charEscapedG = rule "char-escaped" $
  oneOf charsReserved <|> charControlG

charControlG :: Grammar Char Char
charControlG = rule "char-control-abbrev" $ choiceP
  [ terminal abbreviation >* pure charControl
  | (abbreviation, charControl) <- charsControl
  ]

charsReserved :: [Char]
charsReserved = "$()*+.?[\\]^{|}"

charsControl :: [(String, Char)]
charsControl =
  [ ("NUL", '\NUL'), ("SOH", '\SOH'), ("STX", '\STX'), ("ETX", '\ETX')
  , ("EOT", '\EOT'), ("ENQ", '\ENQ'), ("ACK", '\ACK'), ("BEL", '\BEL')
  , ("BS", '\BS'), ("HT", '\HT'), ("LF", '\LF'), ("VT", '\VT')
  , ("FF", '\FF'), ("CR", '\CR'), ("SO", '\SO'), ("SI", '\SI')
  , ("DLE", '\DLE'), ("DC1", '\DC1'), ("DC2", '\DC2'), ("DC3", '\DC3')
  , ("DC4", '\DC4'), ("NAK", '\NAK'), ("SYN", '\SYN'), ("ETB", '\ETB')
  , ("CAN", '\CAN'), ("EM", '\EM'), ("SUB", '\SUB'), ("ESC", '\ESC')
  , ("FS", '\FS'), ("GS", '\GS'), ("RS", '\RS'), ("US", '\US')
  , ("DEL", '\DEL')
  , ("PAD", '\x80'), ("HOP", '\x81'), ("BPH", '\x82'), ("NBH", '\x83')
  , ("IND", '\x84'), ("NEL", '\x85'), ("SSA", '\x86'), ("ESA", '\x87')
  , ("HTS", '\x88'), ("HTJ", '\x89'), ("VTS", '\x8A'), ("PLD", '\x8B')
  , ("PLU", '\x8C'), ("RI", '\x8D'), ("SS2", '\x8E'), ("SS3", '\x8F')
  , ("DCS", '\x90'), ("PU1", '\x91'), ("PU2", '\x92'), ("STS", '\x93')
  , ("CCH", '\x94'), ("MW", '\x95'), ("SPA", '\x96'), ("EPA", '\x97')
  , ("SOS", '\x98'), ("SGCI",'\x99'), ("SCI", '\x9A'), ("CSI", '\x9B')
  , ("ST", '\x9C'), ("OSC", '\x9D'), ("PM", '\x9E'), ("APC", '\x9F')
  ]

failG :: Grammar Char ()
failG = rule "fail" $ terminal "\\q" <|> terminal "[]"

ruleG :: Grammar Char (String, RegEx Char)
ruleG = rule "rule" $ manyP charG >*< terminal " = " >* regexGrammar

newtype RegString = RegString {runRegString :: RegEx Char}
  deriving newtype
    ( Eq, Ord
    , Semigroup, Monoid, KleeneStarAlgebra
    , Tokenized Char, TokenAlgebra Char
    , TerminalSymbol Char, NonTerminalSymbol
    , Matching String
    )

newtype RegBnfString = RegBnfString {runRegBnfString :: Bnf (RegEx Char)}
  deriving newtype
    ( Eq, Ord
    , Semigroup, Monoid, KleeneStarAlgebra
    , Tokenized Char, TokenAlgebra Char
    , TerminalSymbol Char, NonTerminalSymbol
    , BackusNaurForm, Matching String
    )

instance IsList RegString where
  type Item RegString = Char
  fromList
    = fromMaybe zeroK
    . listToMaybe
    . mapMaybe prsF
    . runReador regexGrammar
    where
      prsF (rex,"") = Just (RegString rex)
      prsF _ = Nothing
  toList
    = maybe "\\q" ($ "")
    . evalPrintor regexGrammar
    . runRegString
instance IsString RegString where
  fromString = fromList
instance Show RegString where
  showsPrec precision = showsPrec precision . toList
instance Read RegString where
  readsPrec _ str = [(fromList str, "")]
instance IsList RegBnfString where
  type Item RegBnfString = Char
  fromList
    = fromMaybe zeroK
    . listToMaybe
    . mapMaybe prsF
    . runReador ebnfGrammar
    where
      prsF (ebnf,"") = Just (RegBnfString ebnf)
      prsF _ = Nothing
  toList
    = maybe "{start} = \\q" ($ "")
    . evalPrintor ebnfGrammar
    . runRegBnfString
instance IsString RegBnfString where
  fromString = fromList
instance Show RegBnfString where
  showsPrec precision = showsPrec precision . toList
instance Read RegBnfString where
  readsPrec _ str = [(fromList str, "")]
