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
    -- * Lookahead
  , Lookahead (..)
    -- * Precedence
  , Precedence (..)
  , precG
  , readsPrecG
  , showsPrecG
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.Diopter (skippedMany)
import Control.Lens.Grammar.BackusNaur
import Control.Lens.Grammar.Class
import Control.Lens.Grammar.Symbol
import Control.Lens.Grammar.Token
import Control.Lens.PartialIso
import Control.Lens.Prismoid ((>?*))
import Data.Char (isLetter, toUpper)
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
  ( Grammatical Char p, Lookahead p
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
precParens p = spacesG >* parenthesized p

{- Bare, or within parentheses, without leading whitespace, so that no two
places skip the same whitespace, which `read` skips once, greedily. -}
parenthesized :: PrecGrammatical p => p a b -> p a b
parenthesized p = p >|< terminal "(" >* precReset (precParens p) *< spacesG *< terminal ")"

{- | A list, in brackets, its items separated by commas, after whitespace,
at precedence 0, within any parentheses, as `GHC.Read.list` reads &
`showList` shows. -}
precList :: PrecGrammatical p => p a a -> p [a] [a]
precList = precParens . bracketsG

-- Items in brackets, separated by commas, after whitespace, at precedence 0.
bracketsG :: PrecGrammatical p => p a a -> p [a] [a]
bracketsG x = terminal "[" >* orP
  [ _Empty >? oneP
  , _Cons >? precReset x >*< manyP (spacesG >* terminal "," >* precReset x)
  ] *< spacesG *< terminal "]"

{- | Negative lookahead, as `read`'s lexer munches lexemes maximally: what
`notAhead` a grammar parses mustn't follow, which consumes nothing, &
prints nothing. -}
class Lookahead p where
  notAhead :: p () () -> p () ()
instance (Foldable f, Alternative f) => Lookahead (Parsor s f) where
  notAhead (Parsor q) = Parsor $ \mode s -> case mode of
    Nothing | not (null (q Nothing s)) -> empty
    _ -> pure ((), s)
instance Applicative f => Lookahead (Printor s f) where
  notAhead _ = Printor (\_ -> pure ((), id))
instance Lookahead p => Lookahead (Precedence p) where
  notAhead (Precedence q) = Precedence (notAhead . q)

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
instance (Grammatical Char p, Lookahead p) => PrecGrammatical (Precedence p) where
    precP n (Precedence x) = Precedence (\d -> if d <= n then x n else falseP)
    precStep (Precedence x) = Precedence (x . (+ 1))
    precReset (Precedence x) = Precedence (const (x 0))
    precWith k = Precedence (\d -> runPrecedence (k d) d)

{- | A type's `PrecGrammar` at a precedence, at any `Grammatical`
interpreter which parses or prints. -}
precG :: forall a p. (PrecGrammar a, Grammatical Char p, Lookahead p) => Int -> p a a
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
  precGrammar = precParens charG
  -- strings, or brackets, as `read` reads, & strings, as `show` shows
  precListGrammar = precParens (stringG >|< parenthesized (bracketsG precGrammar))
instance PrecGrammar a => PrecGrammar [a] where
  precGrammar = precListGrammar
instance PrecGrammar Bool
instance PrecGrammar Ordering
instance PrecGrammar a => PrecGrammar (Maybe a)
instance (PrecGrammar a, PrecGrammar b) => PrecGrammar (Either a b)
instance PrecGrammar () where
  precGrammar = precParens (terminal "(" >* spacesG *< terminal ")")
instance (PrecGrammar a, PrecGrammar b) => PrecGrammar (a, b) where
  precGrammar = tupled (itemG >*< commaG >* itemG)
instance (PrecGrammar a, PrecGrammar b, PrecGrammar c) => PrecGrammar (a, b, c) where
  precGrammar = tupled $ iso (\(a, b, c) -> (a, (b, c))) (\(a, (b, c)) -> (a, b, c))
    >~ itemG >*< commaG >* itemG >*< commaG >* itemG
instance (PrecGrammar a, PrecGrammar b, PrecGrammar c, PrecGrammar d)
  => PrecGrammar (a, b, c, d) where
    precGrammar = tupled $ iso
      (\(a, b, c, d) -> (a, (b, (c, d)))) (\(a, (b, (c, d))) -> (a, b, c, d))
      >~ itemG >*< commaG >* itemG >*< commaG >* itemG >*< commaG >* itemG
instance (PrecGrammar a, PrecGrammar b, PrecGrammar c, PrecGrammar d, PrecGrammar e)
  => PrecGrammar (a, b, c, d, e) where
    precGrammar = tupled $ iso
      (\(a, b, c, d, e) -> (a, (b, (c, (d, e)))))
      (\(a, (b, (c, (d, e)))) -> (a, b, c, d, e))
      >~ itemG >*< commaG >* itemG >*< commaG >* itemG >*< commaG >* itemG
        >*< commaG >* itemG

-- A tuple, within parentheses, its items at precedence 0, as `read`'s
-- @wrap_tup@ reads & `show` shows.
tupled :: PrecGrammatical p => p a a -> p a a
tupled items' = precParens (terminal "(" >* items' *< spacesG *< terminal ")")

itemG :: (PrecGrammar a, PrecGrammatical p) => p a a
itemG = precReset precGrammar

commaG :: PrecGrammatical p => p () ()
commaG = spacesG >* terminal ","

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
    Infix _ n -> precP n (gPrecFields (InfixFields (operatorG name)))
    Prefix
      | conIsRecord con -> precWith $ \d ->
          let body = nameG name >* spacedG >* terminal "{" >* spacesG
                >* gPrecFields RecordFields *< spacesG *< terminal "}"
          in if d <= 10 then body else if d == 11 then unprinted >? body else falseP
      | gArity (Proxy @f) == 0 -> nameG name >* gPrecFields PrefixFields
      | otherwise -> precP 10 (nameG name >* gPrecFields PrefixFields)
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
      gPrecFields RecordFields >*< spacesG >* terminal "," >* spacedG >* gPrecFields RecordFields
    InfixFields operator -> gPrecFields BareField >*< operator >* gPrecFields BareField
    _ -> gPrecFields style >*< gPrecFields style
  gArity _ = gArity (Proxy @f) + gArity (Proxy @g)
instance (Selector s, PrecGrammar a) => GPrecFields (M1 S s (K1 R a)) where
  gPrecFields style = iso (unK1 . unM1) (M1 . K1) >~ case style of
    RecordFields -> nameG field >* spacedG >* symbolG "=" >* spaceG >* precReset precGrammar
    BareField -> precStep precGrammar
    _ -> spaceG >* precStep precGrammar
    where
      field = selName (undefined :: M1 S s (K1 R a) ())
  gArity _ = 1

-- A name, an identifier, or a symbol within parentheses.
nameG :: PrecGrammatical p => String -> p () ()
nameG name
  | symbolic name =
      terminal "(" >* spacesG >* symbolG name *< spacesG *< terminal ")"
  | otherwise = identG name

-- An infix operator, a symbol, or an identifier within backquotes.
operatorG :: PrecGrammatical p => String -> p () ()
operatorG name
  | symbolic name = spacedG >* symbolG name >* spaceG
  | otherwise = spacedG >* terminal "`" >* spacesG >* identG name
      *< spacesG *< terminal "`" >* spaceG

symbolic :: String -> Bool
symbolic = \case
  c : _ -> c == ':' || tokenClass symbolClass c
  [] -> False
instance PrecGrammar Natural where precGrammar = precParens naturalG
instance PrecGrammar Integer where
  precGrammar = precParens (precWith (\d -> signed >~ negativeAt d >*< magnitudeG))
instance PrecGrammar Double where precGrammar = precParens (precWith floatingAt)
instance PrecGrammar Float where precGrammar = precParens (precWith floatingAt)
instance PrecGrammar Int where precGrammar = integralG
instance PrecGrammar Int8 where precGrammar = integralG
instance PrecGrammar Int16 where precGrammar = integralG
instance PrecGrammar Int32 where precGrammar = integralG
instance PrecGrammar Int64 where precGrammar = integralG
instance PrecGrammar Word where precGrammar = integralG
instance PrecGrammar Word8 where precGrammar = integralG
instance PrecGrammar Word16 where precGrammar = integralG
instance PrecGrammar Word32 where precGrammar = integralG
instance PrecGrammar Word64 where precGrammar = integralG

-- Sized integers read as `Integer`s, wrapping out of range, as `read` does.
integralG :: (Integral a, PrecGrammatical p) => p a a
integralG = iso toInteger fromInteger >~ precGrammar @Integer

-- A minus, printing bare up to precedence 6, & parsing bare at any.
negativeAt :: (RegGrammatical Char p, Lookahead p) => Int -> p Bool Bool
negativeAt d
  | d <= 6 = negativeG
  | otherwise = orP
      [ only False >? oneP
      , only True . unprinted >? terminal "-" >* spacesG ]

-- A prism which never matches, so that its alternative parses, but never prints.
unprinted :: Prism' a a
unprinted = prism' id (const Nothing)

-- One of two terminals, printing the first, & parsing either.
eitherOf :: (RegGrammatical Char p, Lookahead p) => String -> String -> p () ()
eitherOf printed parsed = terminal printed >|< (unprinted >? terminal parsed)

-- A minus, a lexeme of its own, as whether a number is negative.
negativeG :: (RegGrammatical Char p, Lookahead p) => p Bool Bool
negativeG = iso (\b -> if b then Just () else Nothing) isJust
  >~ optionalP (terminal "-" >* spacesG)

-- Whitespace, by `Data.Char.isSpace`, which `read` skips before each
-- lexeme & after all, & which never prints.
spacesG :: (RegGrammatical Char p, Lookahead p) => p () ()
spacesG = (skippedMany >?* tokenClass spaceClass) *< notAhead (tokenG spaceClass)

-- Whitespace, by `Data.Char.isSpace`.
spaceClass :: TokenClass Char
spaceClass = oneOf "\t\n\v\f\r" >|< asIn Space

-- A token of a class, as unit, for lookahead.
tokenG :: (RegGrammatical Char p, Lookahead p) => TokenClass Char -> p () ()
tokenG cls = dimap (const ' ') (const ()) (tokenClass cls)

-- The digits of a base, in either case.
digitClass :: Int -> TokenClass Char
digitClass base = oneOf (concat
  [ [c, toUpper c] | c <- take base (['0' .. '9'] <> ['a' .. 'z']) ])

-- Identifiers' & symbols' characters, which `read`'s lexer munches.
idfClass, symbolClass :: TokenClass Char
idfClass = anyP asIn
  [ UppercaseLetter, LowercaseLetter, TitlecaseLetter, ModifierLetter
  , OtherLetter, DecimalNumber, LetterNumber, OtherNumber ]
  >|< oneOf "_'"
symbolClass = notOneOf ",;()[]{}`" >&< orP
  [ anyP asIn [MathSymbol, CurrencySymbol, ModifierSymbol, OtherSymbol, DashPunctuation]
  , asIn OtherPunctuation >&< notOneOf "'\""
  , asIn ConnectorPunctuation >&< notOneOf "_" ]

-- An identifier, & a symbol, munched maximally.
identG, symbolG :: (RegGrammatical Char p, Lookahead p) => String -> p () ()
identG name = terminal name *< notAhead (tokenG idfClass)
symbolG name = terminal name *< notAhead (tokenG symbolClass)

-- A space, where `show` separates lexemes, printing one, & parsing one
-- whitespace character, or none where none follows, the rest of it
-- skipped before the next lexeme.
spaceG :: (RegGrammatical Char p, Lookahead p) => p () ()
spaceG = orP
  [ terminal " "
  , unprinted >? tokenG (spaceClass >&< notOneOf " ")
  , unprinted >? notAhead (tokenG spaceClass) ]

-- A space, printing one, & parsing any whitespace.
spacedG :: (RegGrammatical Char p, Lookahead p) => p () ()
spacedG = spaceG >* spacesG

-- Signed, by an improper iso, where @-0@ parses too.
signed :: (Num a, Ord a) => Iso' a (Bool, a)
signed = iso
  (\n -> (n < 0, abs n))
  (\(negative, n) -> if negative then negate n else n)

-- A number's lexeme without a fraction or exponent: decimal, printed,
-- or binary, octal or hexadecimal, after @0b@, @0o@ or @0x@, in either
-- case, parsed & tried first, as `read`'s lexer does.
magnitudeG :: (RegGrammatical Char p, Lookahead p) => p Integer Integer
magnitudeG = (unprinted >? try (terminal "0" >* basedG))
  >|< numeral 10 *< notAhead (tokenG (digitClass 10)) *< decimalEndG

-- Where a decimal integer ends: not before a fraction, nor an exponent.
decimalEndG :: (RegGrammatical Char p, Lookahead p) => p () ()
decimalEndG = notAhead (terminal "." >* tokenG (digitClass 10))
  *< notAhead (orP (map terminal ["e", "E"])
    >* orP [terminal "-", terminal "+", oneP] >* tokenG (digitClass 10))

basedG :: forall p. (RegGrammatical Char p, Lookahead p) => p Integer Integer
basedG = orP
  [ eitherOf "b" "B" >* munched 2
  , eitherOf "o" "O" >* munched 8
  , eitherOf "x" "X" >* munched 16
  ]
  where
    munched :: Int -> p Integer Integer
    munched base = numeral (toInteger base) *< notAhead (tokenG (digitClass base))

-- Natural numbers, & negative zero, as `read` reads integers & keeps
-- those which aren't negative.
naturalG :: (RegGrammatical Char p, Lookahead p) => p Natural Natural
naturalG = (iso toInteger fromInteger >~ magnitudeG)
  >|< (unprinted . only 0 >? terminal "-" >* spacesG >* zerosG)
  where
    zerosG = terminal "0" >* orP
      [ zeros *< notAhead (tokenG (digitClass 10)) *< decimalEndG
      , orP (map terminal ["b", "B"]) >* terminal "0" >* zeros
          *< notAhead (tokenG (digitClass 2))
      , orP (map terminal ["o", "O"]) >* terminal "0" >* zeros
          *< notAhead (tokenG (digitClass 8))
      , orP (map terminal ["x", "X"]) >* terminal "0" >* zeros
          *< notAhead (tokenG (digitClass 16))
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
floatingAt :: (RealFloat a, RegGrammatical Char p, Lookahead p) => Int -> p a a
floatingAt d = iso toLexeme fromLexeme >~ negativeAt d >*< orP
  [ only NotANumber >? identG "NaN"
  , only Infinite >? identG "Infinity"
  , unprinted . _Based >? try (terminal "0" >* basedG)
  , _Decimal >? digitsG
      >*< orP
        [ _Just >? terminal "." >* digitsG
        , _Nothing >? notAhead (terminal "." >* tokenG (digitClass 10)) ]
      >*< orP
        [ _Just >? eitherOf "e" "E" >* (signed >~ exponentSignG >*< numeral 10
            *< notAhead (tokenG (digitClass 10)))
        , _Nothing >? notAhead (orP (map terminal ["e", "E"])
            >* orP [terminal "-", terminal "+", oneP] >* tokenG (digitClass 10)) ]
  ]
  where
    digitsG = someP (digit 10) *< notAhead (tokenG (digitClass 10))
    exponentSignG = orP
      [ only True >? terminal "-"
      , only False . unprinted >? terminal "+"
      , only False >? oneP
      ]

toLexeme :: RealFloat a => a -> (Bool, FloatLexeme)
toLexeme x
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

fromLexeme :: RealFloat a => (Bool, FloatLexeme) -> a
fromLexeme (negative, lexeme) = (if negative then negate else id) value
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
charG :: (RegGrammatical Char p, Lookahead p) => p Char Char
charG = terminal "'" >* litCharG '\'' *< terminal "'"

{- A character within a literal, printing as `show` does, by `showLitChar`,
& parsing as `read` does: unescaped, but for @\\@ & the literal's quote;
by a named escape; or by its decimal, octal or hexadecimal code, up to
`maxBound`, or as a control, @\\^@@ to @\\^_@. -}
litCharG :: (RegGrammatical Char p, Lookahead p) => Char -> p Char Char
litCharG quote = rawG [quote] >|< terminal "\\" >* orP
  [fixedEscG True, decimalEscG, octalEscG, hexEscG, controlEscG]

-- Unescaped, but for @\\@ & some others, printing only printable ASCII.
rawG :: (RegGrammatical Char p, Lookahead p) => String -> p Char Char
rawG excluded = tokenClass (oneOf [' ' .. '~'] >&< notOneOf ('\\' : excluded))
  >|< unprinted >? tokenClass (notOneOf ('\\' : excluded <> [' ' .. '~']))

-- Named escapes, with @SO@ or not.
fixedEscG :: (RegGrammatical Char p, Lookahead p) => Bool -> p Char Char
fixedEscG withSO = escapesG $
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
decimalEscG, octalEscG, hexEscG, controlEscG :: (RegGrammatical Char p, Lookahead p) => p Char Char
decimalEscG = prism' toEnum (\c -> if c > '\DEL' then Just (fromEnum c) else Nothing)
  >? boundedNumeral 10 (fromEnum (maxBound :: Char))
octalEscG = unprinted . prism' toEnum (Just . fromEnum)
  >? eitherOf "o" "O" >* boundedNumeral 8 (fromEnum (maxBound :: Char))
hexEscG = unprinted . prism' toEnum (Just . fromEnum)
  >? eitherOf "x" "X" >* boundedNumeral 16 (fromEnum (maxBound :: Char))
controlEscG = unprinted . iso (\c -> toEnum (fromEnum c + 64)) (\c -> toEnum (fromEnum c - 64))
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
stringG :: forall p. (RegGrammatical Char p, Lookahead p) => p String String
stringG = iso items (\xs -> [c | StrChar c <- xs])
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
      , itemThen (_StrChar >? rawG ('"' : continuing)) free
      , itemThen (_StrChar >? terminal "\\" >* orP [fixedEscG False, controlEscG]) free
      , itemThen (_StrChar . only '\SO' >? terminal "\\SO") afterSO
      , itemThen (_StrChar >? terminal "\\" >* decimalEscG) afterDecimal
      , itemThen (_StrChar >? terminal "\\" >* octalEscG) afterOctal
      , itemThen (_StrChar >? terminal "\\" >* hexEscG) afterHex
      ]
    itemThen :: p StrItem StrItem -> p [StrItem] [StrItem] -> p [StrItem] [StrItem]
    itemThen item rest = _Cons >? item >*< rest
    emptyG :: p StrItem StrItem
    emptyG = only StrEmpty >? (terminal "\\&" >|< unprinted >? terminal "\\"
      >* dimap (const ' ') (const ()) (tokenClass (oneOf "\t\n\v\f\r" >|< asIn Space))
      >* spacesG *< terminal "\\")
    items = \case
      c : cs@(c' : _) | protected c c' -> StrChar c : StrEmpty : items cs
      c : cs -> StrChar c : items cs
      [] -> []
    protected c c' = (c > '\DEL' && isDec c') || (c == '\SO' && c' == 'H')
    isDec c' = '0' <= c' && c' <= '9'

-- Escapes by fixed strings, as a trie, which is LL(1), maximally munched,
-- like @\\SO@ & @\\SOH@, each character printing by its first string.
escapesG :: (RegGrammatical Char p, Lookahead p) => [(Char, String)] -> p Char Char
escapesG escapes = orP $
  [only c >? oneP | (c, "") <- take 1 [e | e@(_, "") <- escapes]]
  <> [ terminal [first] >* escapesG [(c, rest) | (c, x : rest) <- escapes, x == first]
     | first <- nub [x | (_, x : _) <- escapes] ]

{- A natural number in a base, up to a bound, with leading zeros, which
parse, as `read`'s lexer does, but don't print; a regular grammar, by the
bound's digits, so that a number beyond it fails to parse. -}
boundedNumeral :: forall n p. (Integral n, RegGrammatical Char p, Lookahead p) => n -> n -> p n n
boundedNumeral base bound
  = (unprinted >? try (terminal "0" >* zerosG >* positiveG))
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
      in if isLetter c then eitherOf [c] [toUpper c] else terminal [c]
