{- |
Module      : Control.Lens.Grammar.Prec
Description : grammars of Haskell types, as Read & Show
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable

Grammars of Haskell types, equivalent to their stock `Read` & `Show`
instances, by precedence, as `Text.ParserCombinators.ReadPrec` reads, &
`showsPrec` shows: `PrecGrammar`s, run by `PrecGrammatical`s, like
t'Precedence', which `readsPrecG` & `showsPrecG` run.
-}

module Control.Lens.Grammar.Prec
  ( -- * PrecGrammar
    PrecGrammar (..)
  , PrecGrammatical (..)
  , precParens
  , precList
    -- * NotFollowedBy
  , NotFollowedBy (..)
  , eof
  , munch
  , munch1
  , skipSpaces
    -- * Precedence
  , Precedence (..)
  , precG
  , readsPrecG
  , showsPrecG
  ) where

import Control.Applicative
import Control.Monad ((>=>))
import Control.Lens
import Control.Lens.Diopter (skippedMany)
import Control.Lens.Grammar.BackusNaur
import Control.Lens.Grammar.Class
import Control.Lens.Grammar.RegEx
import Control.Lens.Grammar.Symbol
import Control.Lens.Grammar.Token
import Control.Lens.PartialIso
import Control.Lens.Prismoid ((>?*))
import Data.Char (isDigit, isLetter, toUpper)
import Data.Int (Int8, Int16, Int32, Int64)
import Data.List (nub)
import Data.Maybe (isJust)
import Data.Monoid.Disjunctive
import Data.Profunctor.Distributor
import Data.Profunctor.Grammar
import Data.Profunctor.Monoidal
import Data.Profunctor.Monoidal.Cocartesian
import Data.Ratio ((%))
import Data.String (IsString (..))
import Data.Word (Word8, Word16, Word32, Word64)
import Data.Proxy (Proxy (..))
import GHC.Generics hiding (from, to)
import qualified GHC.Generics as Generic
import Numeric (floatToDigits)
import Numeric.Natural (Natural)

{- | A Haskell type's grammar, by precedence, equivalent to its stock `Read`
& `Show` instances, `readsPrec` & `showsPrec`. -}
class PrecGrammar a where
  precGrammar :: PrecGrammatical p => p a a
  default precGrammar
    :: (Generic a, GPrecSum (Rep a), PrecGrammatical p) => p a a
  precGrammar = iso Generic.from Generic.to >~ precParens gPrecSum
  {- | Lists of the type, as `readListPrec` & `showList`, in brackets, by
  `precList`, by default, & strings, for `Char`. -}
  precListGrammar :: PrecGrammatical p => p [a] [a]
  precListGrammar = precList precGrammar

{- | `Grammatical` interpreters of precedence, as
`Text.ParserCombinators.ReadPrec` has, where a grammar runs in a
precedence context, from 0 to 11, as `showsPrec`'s is. -}
class
  ( Grammatical Char p, NotFollowedBy p
  , forall x y. (x ~ (), y ~ ()) => IsString (p x y) )
  => PrecGrammatical p where
    {- | At a precedence, failing in a context above it, as
    `Text.ParserCombinators.ReadPrec.prec` does. -}
    precP :: Int -> p a b -> p a b
    {- | In a context one higher, for arguments, as
    `Text.ParserCombinators.ReadPrec.step` does. -}
    precStep :: p a b -> p a b
    {- | In the context 0, within brackets, as
    `Text.ParserCombinators.ReadPrec.reset` does. -}
    precReset :: p a b -> p a b
    {- | By the context's precedence. -}
    precWith :: (Int -> p a b) -> p a b

{- | Within any parentheses, after whitespace, as `GHC.Read.parens` reads,
& within parentheses where it doesn't print bare, as `showParen` shows. -}
precParens :: PrecGrammatical p => p a b -> p a b
precParens p = skipSpaces >* precParenthesized p

{- Bare, or within parentheses, without leading whitespace, so that no two
places skip the same whitespace, which `read` skips once, greedily. -}
precParenthesized :: PrecGrammatical p => p a b -> p a b
precParenthesized p = p >|< terminal "(" >* precReset (precParens p) *< skipSpaces *< terminal ")"

{- | A list, in brackets, its items separated by commas, after whitespace,
at precedence 0, within any parentheses, as `GHC.Read.list` reads &
`showList` shows. -}
precList :: PrecGrammatical p => p a a -> p [a] [a]
precList = precParens . precBrackets

-- Items in brackets, separated by commas, after whitespace, at precedence 0.
precBrackets :: PrecGrammatical p => p a a -> p [a] [a]
precBrackets x = terminal "[" >* orP
  [ _Empty >? oneP
  , _Cons >? precReset x >*< manyP (skipSpaces >* terminal "," >* precReset x)
  ] *< skipSpaces *< terminal "]"

{- | Negative lookahead, as `read`'s lexer munches lexemes maximally. -}
class NotFollowedBy p where
  {- | Not followed by a string a pattern matches, consuming nothing, &
  printing nothing; nonterminals match nothing. -}
  notFollowedBy :: RegEx Char -> p () ()
instance (Alternative f, Cons s s Char Char) => NotFollowedBy (Parsor s f) where
  notFollowedBy rex = Parsor $ \mode s -> case mode of
    Nothing | not (null (prefixes rex (0 :: Int, s))) -> empty
    _ -> pure ((), s)
    where
      -- the rests after each prefix a pattern matches, counting tokens,
      -- so that repetitions of empty matches end
      prefixes = \case
        SeqEmpty -> pure
        Sequence x y zs -> foldr ((>=>) . prefixes) pure (x : y : zs)
        NonTerminal _ -> const []
        KleeneStar x -> star x
        KleeneOpt x -> upTo 1 x
        KleenePlus x -> prefixes x >=> star x
        KleeneTimes lo hi x -> foldr (>=>) pure (replicate lo (prefixes x))
          >=> maybe (star x) (\m -> upTo (m - lo) x) hi
        Backtracking x -> prefixes x
        RegExam (Alternate x y zs) ->
          \pos -> concatMap (`prefixes` pos) (x : y : zs)
        RegExam (OneOf toks) -> one (TokenClass (OneOf toks))
        RegExam (NotOneOf toks test) -> one (TokenClass (NotOneOf toks test))
      one cls (n, str) = case uncons str of
        Just (c, str') | tokenClass cls c -> [(n + 1, str')]
        _ -> []
      star x pos = pos :
        [end | pos' <- prefixes x pos, fst pos' > fst pos, end <- star x pos']
      upTo m x pos
        | m <= 0 = [pos]
        | otherwise = pos : (prefixes x pos >>= upTo (m - 1) x)
instance Applicative f => NotFollowedBy (Printor s f) where
  notFollowedBy _ = Printor (\_ -> pure ((), id))
instance NotFollowedBy p => NotFollowedBy (Precedence p) where
  notFollowedBy = Precedence . const . notFollowedBy

{- | At the end of input, not followed by any token. -}
eof :: NotFollowedBy p => p () ()
eof = notFollowedBy anyToken

{- | Tokens of a class, as many as follow, as
`Text.ParserCombinators.ReadP.munch` parses, & printing them. -}
munch
  :: (RegGrammatical Char p, NotFollowedBy p)
  => TokenClass Char -> p String String
munch cls = manyP (tokenClass cls) *< notFollowedBy (tokenClass cls)

{- | Tokens of a class, one or more, as many as follow, as
`Text.ParserCombinators.ReadP.munch1` parses, & printing them. -}
munch1
  :: (RegGrammatical Char p, NotFollowedBy p)
  => TokenClass Char -> p String String
munch1 cls = someP (tokenClass cls) *< notFollowedBy (tokenClass cls)

{- | Whitespace, by `Data.Char.isSpace`, as many as follow, as
`Text.ParserCombinators.ReadP.skipSpaces` parses, & printing none. -}
skipSpaces :: (RegGrammatical Char p, NotFollowedBy p) => p () ()
skipSpaces = dimap (const "") (const ()) (munch precSpaceClass)

{- | A grammar in a precedence context, a `PrecGrammatical` interpreter of
any `Grammatical` one, each of whose structures it lifts pointwise. -}
newtype Precedence p a b = Precedence {runPrecedence :: Int -> p a b}

instance Profunctor p => Profunctor (Precedence p) where
  dimap f g (Precedence h) = Precedence (dimap f g . h)
instance Functor (p a) => Functor (Precedence p a) where
  fmap f (Precedence h) = Precedence (fmap f . h)
instance Applicative (p a) => Applicative (Precedence p a) where
  pure x = Precedence (const (pure x))
  Precedence f <*> Precedence x = Precedence (\d -> f d <*> x d)
instance Alternative (p a) => Alternative (Precedence p a) where
  empty = Precedence (const empty)
  Precedence x <|> Precedence y = Precedence (\d -> x d <|> y d)
  many (Precedence x) = Precedence (many . x)
  some (Precedence x) = Precedence (some . x)
instance Choice p => Choice (Precedence p) where
  left' (Precedence h) = Precedence (left' . h)
  right' (Precedence h) = Precedence (right' . h)
instance DisjunctiveMonoid (p a b) => DisjunctiveMonoid (Precedence p a b) where
  falseP = Precedence (const falseP)
  Precedence x >|< Precedence y = Precedence (\d -> x d >|< y d)
instance CocartesianMonoidal p => CocartesianMonoidal (Precedence p) where
  zeroP = Precedence (const zeroP)
  Precedence x >+< Precedence y = Precedence (\d -> x d >+< y d)
instance CocartesianChoice p => CocartesianChoice (Precedence p) where
  alternate = \case
    Left (Precedence x) -> Precedence (alternate . Left . x)
    Right (Precedence y) -> Precedence (alternate . Right . y)
instance Distributor p => Distributor (Precedence p) where
  optionalP (Precedence x) = Precedence (optionalP . x)
  manyP (Precedence x) = Precedence (manyP . x)
instance Alternator p => Alternator (Precedence p) where
  someP (Precedence x) = Precedence (someP . x)
  optionP def (Precedence x) = Precedence (optionP def . x)
  manyTillP (Precedence x) (Precedence y) = Precedence (\d -> manyTillP (x d) (y d))
  timesP lo hi (Precedence x) = Precedence (timesP lo hi . x)
instance TerminalSymbol token (p a b) => TerminalSymbol token (Precedence p a b) where
  terminal = Precedence . const . terminal
instance Tokenized token (p a b) => Tokenized token (Precedence p a b) where
  anyToken = Precedence (const anyToken)
  token = Precedence . const . token
  oneOf = Precedence . const . oneOf
  notOneOf = Precedence . const . notOneOf
  asIn = Precedence . const . asIn
  notAsIn = Precedence . const . notAsIn
instance TokenAlgebra token (p a b) => TokenAlgebra token (Precedence p a b) where
  tokenClass = Precedence . const . tokenClass
instance Tried (p a b) => Tried (Precedence p a b) where
  try (Precedence x) = Precedence (try . x)
instance Ruled (p a b) => Ruled (Precedence p a b) where
  rule name (Precedence x) = Precedence (rule name . x)
instance BackusNaurForm (p a b) => BackusNaurForm (Precedence p a b)
instance (a ~ (), b ~ (), TerminalSymbol Char (p () ()))
  => IsString (Precedence p a b) where
    fromString = Precedence . const . terminal
instance (Grammatical Char p, NotFollowedBy p) => PrecGrammatical (Precedence p) where
    precP n (Precedence x) = Precedence (\d -> if d <= n then x n else falseP)
    precStep (Precedence x) = Precedence (x . (+ 1))
    precReset (Precedence x) = Precedence (const (x 0))
    precWith k = Precedence (\d -> runPrecedence (k d) d)

{- | A type's `PrecGrammar` at a precedence, at any `Grammatical`
interpreter which parses or prints. -}
precG :: forall a p. (PrecGrammar a, Grammatical Char p, NotFollowedBy p) => Int -> p a a
precG = runPrecedence precGrammar

{- | Read at a precedence, as `readsPrec` does. -}
readsPrecG :: forall a. PrecGrammar a => Int -> ReadS a
readsPrecG d = parseP (precG d :: Parsor String [] a a)

{- | Show at a precedence, as `showsPrec` does, if it shows. -}
showsPrecG :: forall a. PrecGrammar a => Int -> a -> Maybe ShowS
showsPrecG d = printP (precG d :: Printor String Maybe a a)

-- Base types --

{- The base types' grammars, equivalent to their `Read` & `Show`
instances: lexemes, within any parentheses, as `read` accepts them, &
negative numbers, which `showsPrec` parenthesizes above 6, & `read`
accepts bare at any precedence. -}

instance PrecGrammar Char where
  precGrammar = precParens precChar
  -- strings, or brackets, as `read` reads, & strings, as `show` shows
  precListGrammar = precParens (precString >|< precParenthesized (precBrackets precGrammar))
instance PrecGrammar a => PrecGrammar [a] where
  precGrammar = precListGrammar
instance PrecGrammar Bool
instance PrecGrammar Ordering
instance PrecGrammar a => PrecGrammar (Maybe a)
instance (PrecGrammar a, PrecGrammar b) => PrecGrammar (Either a b)
instance PrecGrammar () where
  precGrammar = precParens (terminal "(" >* skipSpaces *< terminal ")")
instance (PrecGrammar a, PrecGrammar b) => PrecGrammar (a, b) where
  precGrammar = precTupled (precItem >*< precComma >* precItem)
instance (PrecGrammar a, PrecGrammar b, PrecGrammar c) => PrecGrammar (a, b, c) where
  precGrammar = precTupled $ iso (\(a, b, c) -> (a, (b, c))) (\(a, (b, c)) -> (a, b, c))
    >~ precItem >*< precComma >* precItem >*< precComma >* precItem
instance (PrecGrammar a, PrecGrammar b, PrecGrammar c, PrecGrammar d)
  => PrecGrammar (a, b, c, d) where
    precGrammar = precTupled $ iso
      (\(a, b, c, d) -> (a, (b, (c, d)))) (\(a, (b, (c, d))) -> (a, b, c, d))
      >~ precItem >*< precComma >* precItem >*< precComma >* precItem >*< precComma >* precItem
instance (PrecGrammar a, PrecGrammar b, PrecGrammar c, PrecGrammar d, PrecGrammar e)
  => PrecGrammar (a, b, c, d, e) where
    precGrammar = precTupled $ iso
      (\(a, b, c, d, e) -> (a, (b, (c, (d, e)))))
      (\(a, (b, (c, (d, e)))) -> (a, b, c, d, e))
      >~ precItem >*< precComma >* precItem >*< precComma >* precItem >*< precComma >* precItem
        >*< precComma >* precItem

-- A tuple, within parentheses, its items at precedence 0, as `read`'s
-- @wrap_tup@ reads & `show` shows.
precTupled :: PrecGrammatical p => p a a -> p a a
precTupled items' = precParens (terminal "(" >* items' *< skipSpaces *< terminal ")")

precItem :: (PrecGrammar a, PrecGrammatical p) => p a a
precItem = precReset precGrammar

precComma :: PrecGrammatical p => p () ()
precComma = skipSpaces >* terminal ","

-- Generics --

{- A sum of constructors, as derived `Read` & `Show` instances read & show
them, by `GHC.Generics`. -}
class GPrecSum f where
  gPrecSum :: PrecGrammatical p => p (f x) (f x)
instance GPrecSum f => GPrecSum (M1 D c f) where
  gPrecSum = iso unM1 M1 >~ gPrecSum
instance (GPrecSum f, GPrecSum g) => GPrecSum (f :+: g) where
  gPrecSum = iso
    (\case L1 x -> Left x; R1 y -> Right y)
    (either L1 R1)
    >~ gPrecSum >+< gPrecSum
instance GPrecSum V1 where
  gPrecSum = falseP
instance (Constructor c, GPrecFields f) => GPrecSum (M1 C c f) where
  gPrecSum = iso unM1 M1 >~ case conFixity con of
    Infix _ n -> precP n (gPrecFields (InfixFields (precOperator name)))
    Prefix
      | conIsRecord con -> precWith $ \d ->
          let body = precName name >* precSpaced >* terminal "{" >* skipSpaces
                >* gPrecFields RecordFields *< skipSpaces *< terminal "}"
          in if d <= 10 then body else if d == 11 then precUnprinted >? body else falseP
      | gArity (Proxy @f) == 0 -> precName name >* gPrecFields PrefixFields
      | otherwise -> precP 10 (precName name >* gPrecFields PrefixFields)
    where
      con = undefined :: M1 C c f ()
      name = conName con

-- How a constructor's fields are written.
data FieldsStyle p
  = PrefixFields
  | BareField
  | RecordFields
  | InfixFields (p () ())

{- The fields of a constructor: prefix, after spaces, at the next precedence;
in records, named, at precedence 0, separated by commas; or infix, about an
operator, at the next precedence. -}
class GPrecFields f where
  gPrecFields :: PrecGrammatical p => FieldsStyle p -> p (f x) (f x)
  gArity :: Proxy f -> Int
instance GPrecFields U1 where
  gPrecFields _ = iso (const ()) (const U1) >~ oneP
  gArity _ = 0
instance (GPrecFields f, GPrecFields g) => GPrecFields (f :*: g) where
  gPrecFields style = iso (\(x :*: y) -> (x, y)) (uncurry (:*:)) >~ case style of
    RecordFields ->
      gPrecFields RecordFields >*< skipSpaces >* terminal "," >* precSpaced >* gPrecFields RecordFields
    InfixFields operator -> gPrecFields BareField >*< operator >* gPrecFields BareField
    _ -> gPrecFields style >*< gPrecFields style
  gArity _ = gArity (Proxy @f) + gArity (Proxy @g)
instance (Selector s, PrecGrammar a) => GPrecFields (M1 S s (K1 R a)) where
  gPrecFields style = iso (unK1 . unM1) (M1 . K1) >~ case style of
    RecordFields -> precName field >* precSpaced >* precSymbol "=" >* precSpace >* precReset precGrammar
    BareField -> precStep precGrammar
    _ -> precSpace >* precStep precGrammar
    where
      field = selName (undefined :: M1 S s (K1 R a) ())
  gArity _ = 1

-- A name, an identifier, or a symbol within parentheses.
precName :: PrecGrammatical p => String -> p () ()
precName name
  | precSymbolic name =
      terminal "(" >* skipSpaces >* precSymbol name *< skipSpaces *< terminal ")"
  | otherwise = precIdent name

-- An infix operator, a symbol, or an identifier within backquotes.
precOperator :: PrecGrammatical p => String -> p () ()
precOperator name
  | precSymbolic name = precSpaced >* precSymbol name >* precSpace
  | otherwise = precSpaced >* terminal "`" >* skipSpaces >* precIdent name
      *< skipSpaces *< terminal "`" >* precSpace

precSymbolic :: String -> Bool
precSymbolic = \case
  c : _ -> c == ':' || tokenClass precSymbolClass c
  [] -> False
instance PrecGrammar Natural where precGrammar = precParens precNatural
instance PrecGrammar Integer where
  precGrammar = precParens (precWith (\d -> precSigned >~ precNegativeAt d >*< precMagnitude))
instance PrecGrammar Double where precGrammar = precParens (precWith precFloating)
instance PrecGrammar Float where precGrammar = precParens (precWith precFloating)
instance PrecGrammar Int where precGrammar = precIntegral
instance PrecGrammar Int8 where precGrammar = precIntegral
instance PrecGrammar Int16 where precGrammar = precIntegral
instance PrecGrammar Int32 where precGrammar = precIntegral
instance PrecGrammar Int64 where precGrammar = precIntegral
instance PrecGrammar Word where precGrammar = precIntegral
instance PrecGrammar Word8 where precGrammar = precIntegral
instance PrecGrammar Word16 where precGrammar = precIntegral
instance PrecGrammar Word32 where precGrammar = precIntegral
instance PrecGrammar Word64 where precGrammar = precIntegral

-- Sized integers read as `Integer`s, wrapping out of range, as `read` does.
precIntegral :: (Integral a, PrecGrammatical p) => p a a
precIntegral = iso toInteger fromInteger >~ precGrammar @Integer

-- A minus, printing bare up to precedence 6, & parsing bare at any.
precNegativeAt :: (RegGrammatical Char p, NotFollowedBy p) => Int -> p Bool Bool
precNegativeAt d
  | d <= 6 = precNegative
  | otherwise = orP
      [ only False >? oneP
      , only True . precUnprinted >? terminal "-" >* skipSpaces ]

-- A prism which never matches, so that its alternative parses, but never prints.
precUnprinted :: Prism' a a
precUnprinted = prism' id (const Nothing)

-- One of two terminals, printing the first, & parsing either.
precEitherOf :: RegGrammatical Char p => String -> String -> p () ()
precEitherOf printed parsed = terminal printed >|< (precUnprinted >? terminal parsed)

-- A minus, a lexeme of its own, as whether a number is negative.
precNegative :: (RegGrammatical Char p, NotFollowedBy p) => p Bool Bool
precNegative = iso (\b -> if b then Just () else Nothing) isJust
  >~ optionalP (terminal "-" >* skipSpaces)

-- Whitespace, by `Data.Char.isSpace`.
precSpaceClass :: TokenClass Char
precSpaceClass = oneOf "\t\n\v\f\r" >|< asIn Space

-- A token of a class, as unit, for lookahead.
precToken :: RegGrammatical Char p => TokenClass Char -> p () ()
precToken cls = dimap (const ' ') (const ()) (tokenClass cls)

-- The digits of a base, in either case.
precDigitClass :: Int -> TokenClass Char
precDigitClass base = oneOf (concat
  [ [c, toUpper c] | c <- take base (['0' .. '9'] <> ['a' .. 'z']) ])

-- Identifiers' & symbols' characters, which `read`'s lexer munches.
precIdfClass, precSymbolClass :: TokenClass Char
precIdfClass = anyP asIn
  [ UppercaseLetter, LowercaseLetter, TitlecaseLetter, ModifierLetter
  , OtherLetter, DecimalNumber, LetterNumber, OtherNumber ]
  >|< oneOf "_'"
precSymbolClass = notOneOf ",;()[]{}`" >&< orP
  [ anyP asIn [MathSymbol, CurrencySymbol, ModifierSymbol, OtherSymbol, DashPunctuation]
  , asIn OtherPunctuation >&< notOneOf "'\""
  , asIn ConnectorPunctuation >&< notOneOf "_" ]

-- An identifier, & a symbol, munched maximally.
precIdent, precSymbol :: (RegGrammatical Char p, NotFollowedBy p) => String -> p () ()
precIdent name = terminal name *< notFollowedBy (tokenClass precIdfClass)
precSymbol name = terminal name *< notFollowedBy (tokenClass precSymbolClass)

-- A space, where `show` separates lexemes, printing one, & parsing one
-- whitespace character, or none where none follows, the rest of it
-- skipped before the next lexeme.
precSpace :: (RegGrammatical Char p, NotFollowedBy p) => p () ()
precSpace = orP
  [ terminal " "
  , precUnprinted >? precToken (precSpaceClass >&< notOneOf " ")
  , precUnprinted >? notFollowedBy (tokenClass precSpaceClass) ]

-- A space, printing one, & parsing any whitespace.
precSpaced :: (RegGrammatical Char p, NotFollowedBy p) => p () ()
precSpaced = precSpace >* skipSpaces

-- Signed, by an improper iso, where @-0@ parses too.
precSigned :: (Num a, Ord a) => Iso' a (Bool, a)
precSigned = iso
  (\n -> (n < 0, abs n))
  (\(negative, n) -> if negative then negate n else n)

-- A number's lexeme without a fraction or exponent: decimal, printed,
-- or binary, octal or hexadecimal, after @0b@, @0o@ or @0x@, in either
-- case, parsed & tried first, as `read`'s lexer does.
precMagnitude :: (RegGrammatical Char p, NotFollowedBy p) => p Integer Integer
precMagnitude = (precUnprinted >? try (terminal "0" >* precBased))
  >|< numeral 10 *< precDecimalEnd

-- Where a decimal integer ends: not before a fraction, nor an exponent.
precDecimalEnd :: (RegGrammatical Char p, NotFollowedBy p) => p () ()
precDecimalEnd = notFollowedBy (tokenClass (precDigitClass 10))
  *< precNotFraction *< precNotExponent

-- Not before a fraction.
precNotFraction :: NotFollowedBy p => p () ()
precNotFraction = notFollowedBy (terminal "." <> tokenClass (precDigitClass 10))

-- Not before an exponent.
precNotExponent :: NotFollowedBy p => p () ()
precNotExponent = notFollowedBy
  (oneOf "eE" <> optK (oneOf "+-") <> tokenClass (precDigitClass 10))

precBased :: forall p. (RegGrammatical Char p, NotFollowedBy p) => p Integer Integer
precBased = orP
  [ precEitherOf "b" "B" >* munched 2
  , precEitherOf "o" "O" >* munched 8
  , precEitherOf "x" "X" >* munched 16
  ]
  where
    munched :: Int -> p Integer Integer
    munched base = numeral (toInteger base)
      *< notFollowedBy (tokenClass (precDigitClass base))

-- Natural numbers, & negative zero, as `read` reads integers & keeps
-- those which aren't negative.
precNatural :: (RegGrammatical Char p, NotFollowedBy p) => p Natural Natural
precNatural = (iso toInteger fromInteger >~ precMagnitude)
  >|< (precUnprinted . only 0 >? terminal "-" >* skipSpaces >* zerosG)
  where
    zerosG = terminal "0" >* orP
      [ zeros *< precDecimalEnd
      , orP (map terminal ["b", "B"]) >* terminal "0" >* zeros
          *< notFollowedBy (tokenClass (precDigitClass 2))
      , orP (map terminal ["o", "O"]) >* terminal "0" >* zeros
          *< notFollowedBy (tokenClass (precDigitClass 8))
      , orP (map terminal ["x", "X"]) >* terminal "0" >* zeros
          *< notFollowedBy (tokenClass (precDigitClass 16))
      ]
    zeros = skippedMany >?* terminal "0"

-- A floating point number's lexeme, without its sign.
data FloatLexeme
  = NotANumber
  | Infinite
  -- | digits, a fraction's digits, & an exponent
  | Decimal [Int] (Maybe [Int]) (Maybe Integer)
  -- | binary, octal or hexadecimal, parsed only
  | Based Integer
  deriving stock Eq

_Decimal :: Prism' FloatLexeme ([Int], (Maybe [Int], Maybe Integer))
_Decimal = prism' (\(ds, (fraction, ex)) -> Decimal ds fraction ex) $ \case
  Decimal ds fraction ex -> Just (ds, (fraction, ex))
  _ -> Nothing

_Based :: Prism' FloatLexeme Integer
_Based = prism' Based $ \case
  Based n -> Just n
  _ -> Nothing

{- Floating point numbers, printing as `show` does, by `floatToDigits`,
in fixed notation, or in exponent notation outside @0.1 <= x < 10^7@, &
parsing as `read` does, by `fromRational`, rounding correctly. -}
precFloating :: (RealFloat a, RegGrammatical Char p, NotFollowedBy p) => Int -> p a a
precFloating d = iso precToLexeme precFromLexeme >~ precNegativeAt d >*< orP
  [ only NotANumber >? precIdent "NaN"
  , only Infinite >? precIdent "Infinity"
  , precUnprinted . _Based >? try (terminal "0" >* precBased)
  , _Decimal >? digitsG
      >*< orP
        [ _Just >? terminal "." >* digitsG
        , _Nothing >? precNotFraction ]
      >*< orP
        [ _Just >? precEitherOf "e" "E" >* (precSigned >~ exponentSignG >*< numeral 10
            *< notFollowedBy (tokenClass (precDigitClass 10)))
        , _Nothing >? precNotExponent ]
  ]
  where
    digitsG = someP (digit 10) *< notFollowedBy (tokenClass (precDigitClass 10))
    exponentSignG = orP
      [ only True >? terminal "-"
      , only False . precUnprinted >? terminal "+"
      , only False >? oneP
      ]

precToLexeme :: RealFloat a => a -> (Bool, FloatLexeme)
precToLexeme x
  | isNaN x = (False, NotANumber)
  | isInfinite x = (x < 0, Infinite)
  | otherwise = (x < 0 || isNegativeZero x, generic (floatToDigits 10 (abs x)))
  where
    generic (ds, e)
      | e < 0 || e > 7 = case ds of
          d : ds'@(_ : _) -> Decimal [d] (Just ds') (Just (toInteger e - 1))
          _ -> Decimal (take 1 ds <> [0 | null ds]) (Just [0]) (Just (toInteger e - 1))
      | otherwise =
          let (whole, fraction) = splitAt e (ds <> replicate (e - length ds) 0)
          in Decimal (orZero whole) (Just (orZero fraction)) Nothing
    orZero ds = if null ds then [0] else ds

precFromLexeme :: RealFloat a => (Bool, FloatLexeme) -> a
precFromLexeme (negative, lexeme) = (if negative then negate else id) value
  where
    value = case lexeme of
      NotANumber -> 0 / 0
      Infinite -> 1 / 0
      Based n -> fromInteger n
      Decimal whole fraction ex -> case ex of
        Nothing -> fromRational (rational whole fraction 0)
        -- `read` bounds exponents by the type's range, before computing
        Just e -> case firstDigit whole fraction of
          Nothing -> 0
          Just first
            | toInteger first + e > toInteger (snd range + 3) -> 1 / 0
            | toInteger first + e < toInteger (fst range - 3) -> 0
            | otherwise -> fromRational (rational whole fraction e)
    range = floatRange value
    rational whole fraction e =
      let
        ds = whole <> concat fraction
        scale = e - toInteger (length (concat fraction))
        n = foldl' (\acc d -> acc * 10 + toInteger d) 0 ds
      in if scale >= 0 then fromInteger (n * 10 ^ scale) else n % (10 ^ negate scale)
    firstDigit whole fraction = case dropWhile (== 0) whole of
      significant@(_ : _) -> Just (length significant)
      [] -> case span (== 0) (concat fraction) of
        (_, []) -> Nothing
        (zeros, _) -> Just (negate (length zeros))

-- A character's literal, between single quotes.
precChar :: (RegGrammatical Char p, NotFollowedBy p) => p Char Char
precChar = terminal "'" >* precLitChar '\'' *< terminal "'"

{- A character within a literal, printing as `show` does, by `showLitChar`,
& parsing as `read` does: unescaped, but for @\\@ & the literal's quote;
by a named escape; or by its decimal, octal or hexadecimal code, up to
`maxBound`, or as a control, @\\^@@ to @\\^_@. -}
precLitChar :: (RegGrammatical Char p, NotFollowedBy p) => Char -> p Char Char
precLitChar quote = precRaw [quote] >|< terminal "\\" >* orP
  [precFixedEsc True, precDecimalEsc, precOctalEsc, precHexEsc, precControlEsc]

-- Unescaped, but for @\\@ & some others, printing only printable ASCII.
precRaw :: RegGrammatical Char p => String -> p Char Char
precRaw excluded = tokenClass (oneOf [' ' .. '~'] >&< notOneOf ('\\' : excluded))
  >|< precUnprinted >? tokenClass (notOneOf ('\\' : excluded <> [' ' .. '~']))

-- Named escapes, with @SO@ or not.
precFixedEsc :: (RegGrammatical Char p, NotFollowedBy p) => Bool -> p Char Char
precFixedEsc withSO = precEscapes $
  [('\'', "'"), ('\a', "a"), ('\b', "b"), ('\f', "f"), ('\n', "n")]
  <> [('\r', "r"), ('\t', "t"), ('\v', "v"), ('\\', "\\"), ('"', "\"")]
  <> [e | e@(c, _) <- zip ['\NUL' ..] asciiNames, withSO || c /= '\SO']
  <> [(' ', "SP"), ('\DEL', "DEL")]
  where
    asciiNames =
      [ "NUL", "SOH", "STX", "ETX", "EOT", "ENQ", "ACK", "BEL"
      , "BS", "HT", "LF", "VT", "FF", "CR", "SO", "SI"
      , "DLE", "DC1", "DC2", "DC3", "DC4", "NAK", "SYN", "ETB"
      , "CAN", "EM", "SUB", "ESC", "FS", "GS", "RS", "US" ]

-- Codes up to `maxBound`, decimal, printing above @\\DEL@, octal & hexadecimal.
precDecimalEsc, precOctalEsc, precHexEsc :: RegGrammatical Char p => p Char Char
precDecimalEsc = prism' toEnum (\c -> if c > '\DEL' then Just (fromEnum c) else Nothing)
  >? precBoundedNumeral 10 (fromEnum (maxBound :: Char))
precOctalEsc = precUnprinted . prism' toEnum (Just . fromEnum)
  >? precEitherOf "o" "O" >* precBoundedNumeral 8 (fromEnum (maxBound :: Char))
precHexEsc = precUnprinted . prism' toEnum (Just . fromEnum)
  >? precEitherOf "x" "X" >* precBoundedNumeral 16 (fromEnum (maxBound :: Char))
precControlEsc :: RegGrammatical Char p => p Char Char
precControlEsc = precUnprinted . iso (\c -> toEnum (fromEnum c + 64)) (\c -> toEnum (fromEnum c - 64))
  >? terminal "^" >* tokenClass (oneOf ['@' .. '_'])

-- A string literal's items: characters, & empty escapes.
data StrItem = StrChar Char | StrEmpty
  deriving stock Eq

_StrChar :: Prism' StrItem Char
_StrChar = prism' StrChar $ \case
  StrChar c -> Just c
  StrEmpty -> Nothing

{- A string's literal, between double quotes, printing as `show` does, by
`showLitString`, with an empty escape, @\\&@, after a numeric escape
before a digit, or after @\\SO@ before @H@, & parsing as `read` does, with
empty escapes, & gaps, @\\@, whitespace & @\\@, anywhere, an improper iso,
& with numeric escapes' digits & @\\SOH@ maximally munched, as `read`'s
lexer does, so that an escape is never followed by what would continue it. -}
precString :: forall p. (RegGrammatical Char p, NotFollowedBy p) => p String String
precString = iso items (\xs -> [c | StrChar c <- xs])
  >~ terminal "\"" >* free *< terminal "\""
  where
    -- items, after which a character mustn't continue the last escape
    free, afterDecimal, afterOctal, afterHex, afterSO :: p [StrItem] [StrItem]
    free = itemsG ""
    afterDecimal = itemsG ['0' .. '9']
    afterOctal = itemsG ['0' .. '7']
    afterHex = itemsG (['0' .. '9'] <> ['a' .. 'f'] <> ['A' .. 'F'])
    afterSO = itemsG "H"
    itemsG :: String -> p [StrItem] [StrItem]
    itemsG continuing = orP
      [ _Empty >? oneP
      , itemThen emptyG free
      , itemThen (_StrChar >? precRaw ('"' : continuing)) free
      , itemThen (_StrChar >? terminal "\\" >* orP [precFixedEsc False, precControlEsc]) free
      , itemThen (_StrChar . only '\SO' >? terminal "\\SO") afterSO
      , itemThen (_StrChar >? terminal "\\" >* precDecimalEsc) afterDecimal
      , itemThen (_StrChar >? terminal "\\" >* precOctalEsc) afterOctal
      , itemThen (_StrChar >? terminal "\\" >* precHexEsc) afterHex
      ]
    itemThen :: p StrItem StrItem -> p [StrItem] [StrItem] -> p [StrItem] [StrItem]
    itemThen item rest = _Cons >? item >*< rest
    emptyG :: p StrItem StrItem
    emptyG = only StrEmpty >? (terminal "\\&" >|< precUnprinted >? terminal "\\"
      >* dimap (const ' ') (const ()) (tokenClass (oneOf "\t\n\v\f\r" >|< asIn Space))
      >* skipSpaces *< terminal "\\")
    items = \case
      c : cs@(c' : _) | protected c c' -> StrChar c : StrEmpty : items cs
      c : cs -> StrChar c : items cs
      [] -> []
    protected c c' = (c > '\DEL' && isDigit c') || (c == '\SO' && c' == 'H')

-- Escapes by fixed strings, as a trie, which is LL(1), maximally munched,
-- like @\\SO@ & @\\SOH@, each character printing by its first string.
precEscapes :: (RegGrammatical Char p, NotFollowedBy p) => [(Char, String)] -> p Char Char
precEscapes escapes = orP $
  [only c >? oneP | (c, "") <- take 1 [e | e@(_, "") <- escapes]]
  <> [ terminal [first] >* precEscapes [(c, rest) | (c, x : rest) <- escapes, x == first]
     | first <- nub [x | (_, x : _) <- escapes] ]

{- A natural number in a base, up to a bound, with leading zeros, which
parse, as `read`'s lexer does, but don't print; a regular grammar, by the
bound's digits, so that a number beyond it fails to parse. -}
precBoundedNumeral :: forall n p. (Integral n, RegGrammatical Char p) => n -> n -> p n n
precBoundedNumeral base bound
  = (precUnprinted >? try (terminal "0" >* zerosG >* positiveG))
  >|< (only 0 >? terminal "0" >* zerosG)
  >|< positiveG
  where
    zerosG :: p () ()
    zerosG = skippedMany >?* terminal "0"
    width :: Int
    width = length (takeWhile (<= bound) (iterate (* base) 1))
    -- without leading zeros, by their number of digits, tried longest first
    positiveG :: p n n
    positiveG = orP $
      try (ranged (base ^ (width - 1)) bound (upTo width bound True))
      : [ try $ ranged (base ^ (j - 1)) (base ^ j - 1)
            (headed [1 .. base - 1] (j - 1) (exactly' (j - 1)))
        | j <- [width - 1, width - 2 .. 1] ]
    ranged :: n -> n -> p n n -> p n n
    ranged lo hi = (prism' id (\n -> if lo <= n && n <= hi then Just n else Nothing) >?)
    -- a first digit, & the rest of so many digits
    headed :: [n] -> Int -> p n n -> p n n
    headed firsts rest restG = orP
      [ prism' (\r -> d * base ^ rest + r)
          (\n -> if n `div` base ^ rest == d then Just (n `mod` base ^ rest) else Nothing)
          >? digitIs d >* restG
      | d <- firsts ]
    -- exactly so many digits, any
    exactly' :: Int -> p n n
    exactly' k = iso (\n -> [n `div` base ^ i `mod` base | i <- [k - 1, k - 2 .. 0]])
      (foldl' (\acc d -> acc * base + d) 0) >~ replicateP k (digit base)
    -- so many digits, up to a bound, the first nonzero when leading
    upTo :: Int -> n -> Bool -> p n n
    upTo 0 _ _ = only 0 >? oneP
    upTo k hi leading =
      let
        w = base ^ (k - 1)
        top = hi `div` w
        lowers = [if leading then 1 else 0 .. top - 1]
      in
        headed lowers (k - 1) (exactly' (k - 1))
        >|< (prism' (\r -> top * w + r)
              (\n -> if n `div` w == top then Just (n `mod` w) else Nothing)
              >? digitIs top >* upTo (k - 1) (hi `mod` w) False)
    -- a digit, by its value, in either case
    digitIs :: n -> p () ()
    digitIs d =
      let c = (['0' .. '9'] <> ['a' .. 'z']) !! fromIntegral d
      in if isLetter c then precEitherOf [c] [toUpper c] else terminal [c]
