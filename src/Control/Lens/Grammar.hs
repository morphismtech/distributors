{- |
Module      : Control.Lens.Grammar
Description : grammar hierarchy
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable

See Chomsky, [Three Models for the Description of Language]
(https://chomsky.info/wp-content/uploads/195609-.pdf)
-}

module Control.Lens.Grammar
  ( -- * Grammar
    RegGrammar
  , Grammar
  , CtxGrammar
  , Regular
  , RegString (..)
  , RegBnf (..)
  , regexGrammar
  , regbnfGrammar
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

type RegGrammar token a = forall p. Regular token p => p a a
type Grammar token a = forall p.
  ( Regular token p
  , forall x. BackusNaurForm (p x x)
  ) => p a a
type CtxGrammar token a = forall p.
  ( Regular token p
  , forall x. BackusNaurForm (p x x)
  , Monadic p
  , Filtrator p
  ) => p a a
type Regular token p =
  ( forall x y. (x ~ (), y ~ ()) => TerminalSymbol token (p x y)
  , forall x y. (x ~ token, y ~ token) => TokenAlgebra token (p x y)
  , Alternator p
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

regexGrammar :: Grammar Char RegString
regexGrammar = _RegString >~ ruleRec "regex" altG
  where
    altG rex = rule "alternate" $
      chain1 Left (_RegExam . _Alternate) (sepBy (terminal "|")) (seqG rex)

    seqG rex = rule "sequence" $ choiceP
      [ _Terminal >? manyP charG
      , chain Left _Sequence (_Terminal . _Empty) noSep (exprG rex)
      ]

    exprG rex = rule "expression" $ choiceP
      [ _KleeneOpt >? atomG rex *< terminal "?"
      , _KleeneStar >? atomG rex *< terminal "*"
      , _KleenePlus >? atomG rex *< terminal "+"
      , atomG rex
      ]

    anyG = rule "char-any" $ choiceP $ map terminal
      ["[^]", "\\P{}", "[^\\P{}]"]

    atomG rex = rule "atom" $ choiceP
      [ _NonTerminal >? terminal "\\q{" >* manyP charG *< terminal "}"
      , _Terminal >? charG >:< asEmpty
      , _RegExam >? classG
      , terminal "(" >* rex *< terminal ")"
      ]

    catTestG = rule "category-test" $ choiceP
      [ _AsIn >? terminal "\\p{" >* categoryG *< terminal "}"
      , _NotAsIn >? terminal "\\P{" >*
          several1 (sepBy (terminal "|")) categoryG
            *< terminal "}"
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

    classG = rule "char-class" $ choiceP
      [ _Fail >? failG
      , _Pass >? anyG
      , _OneOf >? terminal "[" >* several1 noSep charG *< terminal "]"
      , _NotOneOf >?
          terminal "[^" >* several1 noSep charG
            >*< (catTestG <|> pure (NotAsIn Set.empty))
            *< terminal "]"
      , _NotOneOf >? pure Set.empty >*< catTestG
      ]

    failG = rule "fail" $ terminal "[]"

charG :: Grammar Char Char
charG = rule "char" $
  tokenClass (notOneOf charsReserved >&&< notAsIn Control)
  <|> terminal "\\" >* charEscapedG
  where
    charEscapedG = rule "char-escaped" $
      oneOf charsReserved <|> charControlG

    charsReserved = "()*+?[\\]^{|}"

    charControlG = rule "char-control" $ choiceP
      [ terminal abbreviation >* pure charControl
      | (abbreviation, charControl) <- charsControl
      ]

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

regbnfGrammar :: Grammar Char RegBnf
regbnfGrammar = rule "reg-bnf" $ _RegBnf . _Bnf >~
  terminal "{start} = " >* regexGrammar
    >*< several noSep (terminal "\n" >* ruleG)
  where
    ruleG = rule "rule" $ terminal "{" >* manyP charG *< terminal "} = "
      >*< regexGrammar

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
