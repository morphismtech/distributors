module Control.Lens.Grammar
  ( -- *
    RegGrammar
  , Grammar
  , CtxGrammar
  , Grammarr
  , Gram (..)
  , genRegEx
  , genGram
  , genShowS
  , genReadS
  , Rules (..)
  , Regular
  , Grammatical
  , Contextual
  , NonTerminalSymbol (..)
  , regexGrammar
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.PartialIso
import Control.Lens.RegEx
import Control.Lens.Token
import Control.Lens.Stream
import Control.Monad
import Data.Function
import Data.Monoid
import Data.Profunctor.Distributor
import Data.Profunctor.Monadic
import Data.Profunctor.Syntax
import Data.Set (insert, Set)
import GHC.Exts
import Type.Reflection
import Witherable

type RegGrammar c a = forall p. Regular c p => p a a
type Grammar c a = forall p. Grammatical c p => p a a
type CtxGrammar s a = forall p m. Contextual s m p => p s s m a a

type Grammarr c a b = forall p. Grammatical c p => p a a -> p b b

data Gram c = Gram
  { startGram :: (All, RegEx c)
  , rulesGram :: Set (String, (All, RegEx c))
  }
deriving stock instance
  (Show c, Categorized c, Show (Categorize c)) => Show (Gram c)

genGram
  :: (Categorized c, Ord c, Ord (Categorize c))
  => Grammar c a
  -> Gram c
genGram = (\(rules, start) -> Gram start rules) . runInvariantP

genRegEx :: Categorized c => RegGrammar c a -> RegEx c
genRegEx = runInvariantP

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
  , forall x. Rules (p x x)
  )

type Contextual s m p =
  ( Subtextual s m
  , Grammatical (Item s) (p s s m)
  , Polyadic p
  , Tetradic m p
  )

class Rules a where
  rule :: String -> a -> a
  rule _ = id
  ruleRec :: String -> (a -> a) -> a
  ruleRec _ = fix
instance Rules (Parsor s t m a b)
instance Rules (Printor s t m a b)
instance Rules (Lintor s t m a b)
instance (NonTerminalSymbol a, Ord a)
  => Rules (Set (String, a), a) where
    rule name = ruleRec name . const
    ruleRec name f =
      let
        start = nonTerminal name
        (oldRules, newRule)  = f (mempty, start)
        rules = insert (name, newRule) oldRules
      in
        (rules, start)
instance Rules p => Rules (InvariantP p a b) where
  rule name = InvariantP . rule name . runInvariantP
  ruleRec name
    = InvariantP
    . ruleRec name
    . dimap InvariantP runInvariantP

class NonTerminalSymbol a where
  nonTerminal :: String -> a
  default nonTerminal :: Typeable a => String -> a
  nonTerminal q = error (thetype ??? rexrule ??? function)
    where
      x ??? y = x <> " ??? " <> y
      thetype = show (typeRep @a)
      rexrule = "\\q{" <> q <> "}"
      function = "Control.Lens.Grammar.nonTerminal"
instance NonTerminalSymbol (RegEx c) where
  nonTerminal = NonTerminal
instance (Monoid a, NonTerminalSymbol b)
  => NonTerminalSymbol (a,b) where
    nonTerminal = pure . nonTerminal

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
      _InCategory >?< terminal "\\p{" >* categoryG *< terminal "}"

    categoryNotInG = rule "category-not-in" $
      _NotInCategory >?< terminal "\\P{" >* categoryG *< terminal "}"

    charG = rule "char" $ charLiteralG <|> charEscapedG

    charEscapedG = rule "char-escaped" $ terminal "\\" >* inClass charsReserved

    charLiteralG = rule "char-literal" $ notInClass charsReserved

    charsReserved = "$()*+.?[\\]^{|}"

    classInG = rule "class-in" $
      _InClass >?< terminal "[" >* manyP charG *< terminal "]"

    classNotInG = rule "class-not-in" $
      _NotInClass >?< terminal "[^" >* manyP charG *< terminal "]"

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
