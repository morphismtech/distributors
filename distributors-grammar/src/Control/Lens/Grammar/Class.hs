{- |
Module      : Control.Lens.Grammar.Class
Description : grammar classes & base types' grammars
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable

The classes of types' grammars, over their tokens, regular, context-free
& context-sensitive, & the grammars of base types.
-}

module Control.Lens.Grammar.Class
  ( RegGrammar (..)
  , Grammar (..)
  , CtxGrammar (..)
    -- * Numerals
  , digit
  , numeral
  ) where

import Control.Lens
import Control.Lens.PartialIso
import Control.Lens.Grammar.BackusNaur
import Control.Lens.Grammar.Symbol
import Control.Lens.Grammar.Token
import Data.Char (isDigit, isLetter, ord, toLower, toUpper)
import Data.List (nub)
import Data.Ratio ((%))
import Numeric (floatToDigits)
import Control.Lens.Diopter (skippedMany)
import Control.Lens.Prismoid ((>?*))
import Data.Int (Int8, Int16, Int32, Int64)
import Data.Maybe (isJust)
import Data.Monoid.Disjunctive (orP, (>|<), (>&<))
import Data.Profunctor.Distributor
import Data.Profunctor.Monoidal
import Data.Word (Word8, Word16, Word32, Word64)
import Numeric.Natural (Natural)

-- $setup
-- >>> import Control.Lens.Grammar

{- | A type's regular grammar, over its tokens, which is also its
context-free & context-sensitive grammar. -}
class Grammar token a => RegGrammar token a where
  regGrammar :: RegGrammatical token p => p a a

{- | A type's context-free grammar, over its tokens, which is also its
context-sensitive grammar; its regular grammar, by default. -}
class CtxGrammar token a => Grammar token a where
  grammar :: Grammatical token p => p a a
  default grammar :: (RegGrammar token a, Grammatical token p) => p a a
  grammar = regGrammar @token

{- | A type's context-sensitive grammar, over its tokens;
its context-free grammar, by default. -}
class CtxGrammar token a where
  ctxGrammar :: CtxGrammatical token p => p a a
  default ctxGrammar :: (Grammar token a, CtxGrammatical token p) => p a a
  ctxGrammar = grammar @token

-- Base types --

{- The base types' grammars are their `Read` & `Show` instances' lexemes,
printing as `show` does, & parsing as `read` does, but for whitespace &
parentheses, which `read` accepts around any lexeme of any type. -}

instance CtxGrammar Char Char
instance Grammar Char Char where grammar = ruleTyped (regGrammar @Char)
instance RegGrammar Char Char where regGrammar = charG

instance CtxGrammar Char Natural
instance Grammar Char Natural where grammar = ruleTyped (regGrammar @Char)
instance RegGrammar Char Natural where regGrammar = naturalG

instance CtxGrammar Char Integer
instance Grammar Char Integer where grammar = ruleTyped (regGrammar @Char)
instance RegGrammar Char Integer where regGrammar = integerG

instance CtxGrammar Char Double
instance Grammar Char Double where grammar = ruleTyped (regGrammar @Char)
instance RegGrammar Char Double where regGrammar = floatingG

instance CtxGrammar Char Float
instance Grammar Char Float where grammar = ruleTyped (regGrammar @Char)
instance RegGrammar Char Float where regGrammar = floatingG

-- Sized integers read as `Integer`s, wrapping out of range, as `read` does.
instance CtxGrammar Char Int
instance Grammar Char Int where grammar = ruleTyped (regGrammar @Char)
instance RegGrammar Char Int where regGrammar = wrappedG
instance CtxGrammar Char Int8
instance Grammar Char Int8 where grammar = ruleTyped (regGrammar @Char)
instance RegGrammar Char Int8 where regGrammar = wrappedG
instance CtxGrammar Char Int16
instance Grammar Char Int16 where grammar = ruleTyped (regGrammar @Char)
instance RegGrammar Char Int16 where regGrammar = wrappedG
instance CtxGrammar Char Int32
instance Grammar Char Int32 where grammar = ruleTyped (regGrammar @Char)
instance RegGrammar Char Int32 where regGrammar = wrappedG
instance CtxGrammar Char Int64
instance Grammar Char Int64 where grammar = ruleTyped (regGrammar @Char)
instance RegGrammar Char Int64 where regGrammar = wrappedG
instance CtxGrammar Char Word
instance Grammar Char Word where grammar = ruleTyped (regGrammar @Char)
instance RegGrammar Char Word where regGrammar = wrappedG
instance CtxGrammar Char Word8
instance Grammar Char Word8 where grammar = ruleTyped (regGrammar @Char)
instance RegGrammar Char Word8 where regGrammar = wrappedG
instance CtxGrammar Char Word16
instance Grammar Char Word16 where grammar = ruleTyped (regGrammar @Char)
instance RegGrammar Char Word16 where regGrammar = wrappedG
instance CtxGrammar Char Word32
instance Grammar Char Word32 where grammar = ruleTyped (regGrammar @Char)
instance RegGrammar Char Word32 where regGrammar = wrappedG
instance CtxGrammar Char Word64
instance Grammar Char Word64 where grammar = ruleTyped (regGrammar @Char)
instance RegGrammar Char Word64 where regGrammar = wrappedG

-- A prism which never matches, so that its alternative parses, but never prints.
unprinted :: Prism' a a
unprinted = prism' id (const Nothing)

-- One of two terminals, printing the first, & parsing either.
eitherOf :: RegGrammatical Char p => String -> String -> p () ()
eitherOf printed parsed = terminal printed >|< (unprinted >? terminal parsed)

-- A minus, a lexeme of its own, as whether a number is negative.
negativeG :: RegGrammatical Char p => p Bool Bool
negativeG = iso (\b -> if b then Just () else Nothing) isJust
  >~ optionalP (terminal "-")

-- Signed, by an improper iso, where @-0@ parses too.
signed :: (Num a, Ord a) => Iso' a (Bool, a)
signed = iso
  (\n -> (n < 0, abs n))
  (\(negative, n) -> if negative then negate n else n)

-- A number's lexeme without a fraction or exponent: decimal, printed,
-- or binary, octal or hexadecimal, after @0b@, @0o@ or @0x@, in either
-- case, parsed & tried first, as `read`'s lexer does.
magnitudeG :: RegGrammatical Char p => p Integer Integer
magnitudeG = (unprinted >? try (terminal "0" >* basedG)) >|< numeral 10

basedG :: RegGrammatical Char p => p Integer Integer
basedG = orP
  [ eitherOf "b" "B" >* numeral 2
  , eitherOf "o" "O" >* numeral 8
  , eitherOf "x" "X" >* numeral 16
  ]

-- Natural numbers, & negative zero, as `read` reads integers & keeps
-- those which aren't negative.
naturalG :: RegGrammatical Char p => p Natural Natural
naturalG = (iso toInteger fromInteger >~ magnitudeG)
  >|< (unprinted . only 0 >? terminal "-" >* zerosG)
  where
    zerosG = terminal "0" >* orP
      [ skippedMany >?* terminal "0"
      , orP (map terminal ["b", "B", "o", "O", "x", "X"])
          >* terminal "0" >* (skippedMany >?* terminal "0")
      ]

integerG :: RegGrammatical Char p => p Integer Integer
integerG = signed >~ negativeG >*< magnitudeG

wrappedG :: (Integral a, RegGrammatical Char p) => p a a
wrappedG = iso toInteger fromInteger >~ integerG

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
floatingG :: (RealFloat a, RegGrammatical Char p) => p a a
floatingG = iso toLexeme fromLexeme >~ negativeG >*< orP
  [ only NotANumber >? terminal "NaN"
  , only Infinite >? terminal "Infinity"
  , unprinted . _Based >? try (terminal "0" >* basedG)
  , _Decimal >? someP (digit 10)
      >*< optionalP (terminal "." >* someP (digit 10))
      >*< optionalP (eitherOf "e" "E" >* (signed >~ exponentSignG >*< numeral 10))
  ]
  where
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

{- A character's literal, between single quotes, printing as `show` does,
by `showLitChar`, & parsing as `read` does: unescaped, but for @\\@ & @'@;
by a named escape; or by its decimal, octal or hexadecimal code, or as a
control, @\\^@@ to @\\^_@. -}
charG :: RegGrammatical Char p => p Char Char
charG = terminal "'" >* orP
  [ tokenClass (oneOf [' ' .. '~'] >&< notOneOf "\\'")
  , unprinted >? tokenClass (notOneOf ("\\'" <> [' ' .. '~']))
  , terminal "\\" >* orP
    [ escapesG
      ( [('\'', "'"), ('\a', "a"), ('\b', "b"), ('\f', "f"), ('\n', "n")]
        <> [('\r', "r"), ('\t', "t"), ('\v', "v"), ('\\', "\\"), ('"', "\"")]
        <> zip ['\NUL' ..] asciiNames <> [(' ', "SP"), ('\DEL', "DEL")] )
    , prism' fromCode (\c -> if c > '\DEL' then Just (fromEnum c) else Nothing)
        >? numeral 10
    , unprinted . codeOf >? eitherOf "o" "O" >* numeral 8
    , unprinted . codeOf >? eitherOf "x" "X" >* numeral 16
    , unprinted . iso (\c -> toEnum (fromEnum c + 64)) (\c -> toEnum (fromEnum c - 64))
        >? terminal "^" >* tokenClass (oneOf ['@' .. '_'])
    ]
  ] *< terminal "'"
  where
    codeOf = prism' fromCode (Just . fromEnum)
    -- codes beyond `maxBound`, which `read` fails, are its, an improper prism
    fromCode code = toEnum (min (fromEnum (maxBound :: Char)) code)
    asciiNames =
      [ "NUL", "SOH", "STX", "ETX", "EOT", "ENQ", "ACK", "BEL"
      , "BS", "HT", "LF", "VT", "FF", "CR", "SO", "SI"
      , "DLE", "DC1", "DC2", "DC3", "DC4", "NAK", "SYN", "ETB"
      , "CAN", "EM", "SUB", "ESC", "FS", "GS", "RS", "US" ]

-- Escapes by fixed strings, as a trie, which is LL(1), maximally munched,
-- like @\\SO@ & @\\SOH@, each character printing by its first string.
escapesG :: RegGrammatical Char p => [(Char, String)] -> p Char Char
escapesG escapes = orP $
  [only c >? oneP | (c, "") <- take 1 [e | e@(_, "") <- escapes]]
  <> [ terminal [first] >* escapesG [(c, rest) | (c, x : rest) <- escapes, x == first]
     | first <- nub [x | (_, x : _) <- escapes] ]

{- | A digit in a base, from 2 to 36, by its value: @0-9@, then letters,
printing in lowercase, & parsing either case.

>>> [d | (d, "") <- parseP (digit (16 :: Int) :: Parsor String [] Int Int) "F"]
[15]
-}
digit :: (Integral n, Choice p, Tokenized Char (p Char Char)) => n -> p n n
digit base = prism' valueOf charOf >? oneOf chars
  where
    values = take (fromIntegral base) (['0' .. '9'] <> ['a' .. 'z'])
    chars = values <> [toUpper c | c <- values, isLetter c]
    valueOf c
      | isDigit c = fromIntegral (ord c - ord '0')
      | otherwise = fromIntegral (ord (toLower c) - ord 'a' + 10)
    charOf d
      | 0 <= d && d < base = Just (values !! fromIntegral d)
      | otherwise = Nothing

{- | A natural number in a base, from 2 to 36, by its digits, most
significant first, printing without leading zeros, & parsing them too,
an improper iso.

>>> ($ "") <$> printP (numeral (16 :: Integer) :: Printor String Maybe Integer Integer) 255
Just "ff"
-}
numeral :: (Integral n, Alternator p, Tokenized Char (p Char Char)) => n -> p n n
numeral base = iso digitsOf (foldl' (\n d -> n * base + d) 0) >~ someP (digit base)
  where
    digitsOf n
      | n < base = [n]
      | otherwise = let (q, r) = n `quotRem` base in digitsOf q <> [r]
