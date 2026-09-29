module Control.Lens.Grammar.Number
  ( DecimalDigit (..)
  , OctalDigit (..)
  , HexDigit (..)
  , NaturalDigits (..)
  , IntegerDigits (..)
  , naturalDigitsImproperIso
  , naturalGrammar
  , integerDigitsImproperIso
  , integerGrammar
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.Grammar
import Numeric.Natural

data DecimalDigit
  = Dec0 | Dec1 | Dec2 | Dec3 | Dec4
  | Dec5 | Dec6 | Dec7 | Dec8 | Dec9
  deriving stock (Eq, Ord, Show, Read, Enum, Bounded)

data OctalDigit
  = Oct0 | Oct1 | Oct2 | Oct3
  | Oct4 | Oct5 | Oct6 | Oct7
  deriving stock (Eq, Ord, Show, Read, Enum, Bounded)

data HexDigit
  = Hex0 | Hex1 | Hex2 | Hex3 | Hex4 | Hex5 | Hex6 | Hex7
  | Hex8 | Hex9 | HexA | HexB | HexC | HexD | HexE | HexF
  deriving stock (Eq, Ord, Show, Read, Enum, Bounded)

data NaturalDigits
  = NaturalDecimal DecimalDigit [DecimalDigit]
  | NaturalOctal OctalDigit [OctalDigit]
  | NaturalHexadecimal HexDigit [HexDigit]
  deriving stock (Eq, Ord, Show, Read)

data IntegerDigits = IntegerDigits
  { negative :: Bool
  , naturalDigits :: NaturalDigits
  } deriving stock (Eq, Ord, Show, Read)

makeNestedPrisms ''DecimalDigit
makeNestedPrisms ''OctalDigit
makeNestedPrisms ''HexDigit
makeNestedPrisms ''NaturalDigits
makeNestedPrisms ''IntegerDigits

{- | Parses `Natural` numbers matching the lexical syntax of GHC's
`Read` instance: decimal digits, or hexadecimal (@0x@\/@0X@) or
octal (@0o@\/@0O@) digits with the usual prefix. Unparses always
in decimal, matching `Show`; the hexadecimal and octal alternatives
are print-side unreachable, since `naturalDigitsImproperIso`
always normalizes to `NaturalDecimal`.

Left-factored down to single-character terminals throughout, so
every choice point commits after exactly one token of lookahead —
this grammar is @LL(1)@, safe for `parsecG`\/`unparsecG`.

The nonzero-headed decimal alternative is tried /before/ the
zero-led one. `Parsector`'s `Control.Applicative.<|>` does not
backtrack past consumed input, so if the zero-led alternative
(which unconditionally consumes\/emits a leading @0@) were tried
first, it would wrongly commit while unparsing any nonzero value,
never falling back. Trying the nonzero case first means the
zero-led alternative is only ever attempted for a genuine leading
@0@, where it cannot fail.

Deliberately narrower than GHC's actual lexer in three ways, all
kept on purpose rather than matched:

* No sign. GHC's @Read Natural@ lexes a leading @-@ (it reuses
  @Read Integer@'s reader, filtering to non-negative results), so
  @read \"-0\" :: Natural@ succeeds. A natural number shouldn't need
  to understand negation to parse its own magnitude; that belongs
  to the surrounding `Integer` grammar (`IntegerDigits`), not here.
* No fraction\/exponent swallowing. GHC's lexer treats @3.5@ or
  @1e2@ as one atomic numeric lexeme and rejects it outright for an
  integral type, rather than reading just the @3@\/@1@ prefix. That
  behavior falls out of sharing one lexeme grammar across
  'Int'\/'Integer'\/'Double'; for a composable token like this one,
  matching just the leading digits and leaving @.5@\/@e2@ for
  whatever grammar comes next is the more useful behavior.
* No leading-whitespace skip. GHC's @reads@ skips leading space via
  @lex@, a top-level `Read` convention. A token-level grammar meant
  to be embedded inside larger grammars shouldn't unilaterally eat
  whitespace; that's the enclosing grammar's decision.
-}
naturalGrammar :: RegGrammar Char Natural
naturalGrammar = naturalDigitsImproperIso >? naturalDigitsGrammar

{- | The unsigned digit grammar shared by `naturalGrammar` and
`integerGrammar`. See `naturalGrammar` for the design notes: this is
the same @LL(1)@, nonzero-before-zero-led grammar, just without the
outer `naturalDigitsImproperIso` conversion to `Natural`.
-}
naturalDigitsGrammar :: RegGrammar Char NaturalDigits
naturalDigitsGrammar = nonzeroDecimalG <|> zeroLedG
  where
    nonzeroDigitG :: RegGrammar Char DecimalDigit
    nonzeroDigitG = choice
      [ _Dec1 >? terminal "1", _Dec2 >? terminal "2", _Dec3 >? terminal "3"
      , _Dec4 >? terminal "4", _Dec5 >? terminal "5", _Dec6 >? terminal "6"
      , _Dec7 >? terminal "7", _Dec8 >? terminal "8", _Dec9 >? terminal "9"
      ]

    nonzeroDecimalG :: RegGrammar Char NaturalDigits
    nonzeroDecimalG = _NaturalDecimal >? (nonzeroDigitG >*< manyP decimalDigitG)

    -- | Handles every input beginning with @0@: hexadecimal or octal
    -- prefixes, or a (possibly multi-digit, leading-zero) decimal.
    zeroLedG :: RegGrammar Char NaturalDigits
    zeroLedG = terminal "0" >* zeroTailG
      where
        zeroTailG = hexBranch <|> octalBranch <|> decimalTailBranch
        hexBranch = _NaturalHexadecimal >?
          ((terminal "x" <|> terminal "X") >* (hexDigitG >*< manyP hexDigitG))
        octalBranch = _NaturalOctal >?
          ((terminal "o" <|> terminal "O") >* (octalDigitG >*< manyP octalDigitG))
        decimalTailBranch = _NaturalDecimal >?
          (pureP _Dec0 >*< manyP decimalDigitG)

    decimalDigitG :: RegGrammar Char DecimalDigit
    decimalDigitG = choice
      [ _Dec0 >? terminal "0", _Dec1 >? terminal "1", _Dec2 >? terminal "2"
      , _Dec3 >? terminal "3", _Dec4 >? terminal "4", _Dec5 >? terminal "5"
      , _Dec6 >? terminal "6", _Dec7 >? terminal "7", _Dec8 >? terminal "8"
      , _Dec9 >? terminal "9"
      ]
    octalDigitG :: RegGrammar Char OctalDigit
    octalDigitG = choice
      [ _Oct0 >? terminal "0", _Oct1 >? terminal "1", _Oct2 >? terminal "2"
      , _Oct3 >? terminal "3", _Oct4 >? terminal "4", _Oct5 >? terminal "5"
      , _Oct6 >? terminal "6", _Oct7 >? terminal "7"
      ]
    hexDigitG :: RegGrammar Char HexDigit
    hexDigitG = choice
      [ _Hex0 >? terminal "0", _Hex1 >? terminal "1", _Hex2 >? terminal "2"
      , _Hex3 >? terminal "3", _Hex4 >? terminal "4", _Hex5 >? terminal "5"
      , _Hex6 >? terminal "6", _Hex7 >? terminal "7", _Hex8 >? terminal "8"
      , _Hex9 >? terminal "9"
      , _HexA >? (terminal "A" <|> terminal "a")
      , _HexB >? (terminal "B" <|> terminal "b")
      , _HexC >? (terminal "C" <|> terminal "c")
      , _HexD >? (terminal "D" <|> terminal "d")
      , _HexE >? (terminal "E" <|> terminal "e")
      , _HexF >? (terminal "F" <|> terminal "f")
      ]

naturalDigitsImproperIso :: Iso' Natural NaturalDigits
naturalDigitsImproperIso = iso naturalToDigits digitsToNatural
  where
    naturalToDigits :: Natural -> NaturalDigits
    naturalToDigits n = case go n of
      (d : ds) -> NaturalDecimal d ds
      [] -> NaturalDecimal Dec0 []
      where
        go 0 = []
        go m = go q ++ [toEnum (fromIntegral r)]
          where (q, r) = m `divMod` 10

    digitsToNatural :: NaturalDigits -> Natural
    digitsToNatural = \case
      NaturalDecimal d ds -> digitsToNaturalBase 10 (d : ds)
      NaturalOctal d ds -> digitsToNaturalBase 8 (d : ds)
      NaturalHexadecimal d ds -> digitsToNaturalBase 16 (d : ds)

    digitsToNaturalBase :: Enum a => Natural -> [a] -> Natural
    digitsToNaturalBase base =
      foldl (\acc d -> acc * base + fromIntegral (fromEnum d)) 0

{- | Signed decimal, hexadecimal or octal digits, matching GHC's
`Read` lexical syntax for `Integer`, except (as with `naturalGrammar`)
it doesn't swallow leading whitespace or a fractional\/exponent
suffix — see `naturalGrammar` for why that's kept deliberately.

Unparses always as an optional @-@ followed by canonical decimal
digits, matching `Show`. The sign is handled by `optionP`, whose
`Parsector` instance tries the alternatives in a mode-dependent
order: for parsing, it tries the @-@ branch first, falling back to
no sign; for unparsing, it checks the value first (is it negative?)
and only then emits @-@ or nothing. That mode-awareness is exactly
what avoids the commit-before-checking trap that `naturalGrammar`'s
docs describe for the zero-led\/nonzero-led split.
-}
integerGrammar :: RegGrammar Char Integer
integerGrammar =
  integerDigitsImproperIso >? (_IntegerDigits >? (signG >*< naturalDigitsGrammar))
  where
    signG :: RegGrammar Char Bool
    signG = optionP (only False) (only True >? terminal "-")

{- | An improper isomorphism between `Integer` and `IntegerDigits`,
built the same way GHC's own @Read Natural@ is built from @Read
Integer@, but inverted: here `Integer` is decomposed into a sign and
a `Natural` magnitude (via `naturalDigitsImproperIso`). Only the left
inverse law holds; the right inverse normalizes away a redundant
@negative = True@ paired with a zero magnitude to @negative = False@,
since @-0 = 0@.
-}
integerDigitsImproperIso :: Iso' Integer IntegerDigits
integerDigitsImproperIso = iso integerToDigits digitsToInteger
  where
    integerToDigits :: Integer -> IntegerDigits
    integerToDigits n =
      IntegerDigits (n < 0) (fromInteger (abs n) ^. naturalDigitsImproperIso)

    digitsToInteger :: IntegerDigits -> Integer
    digitsToInteger (IntegerDigits neg nd) =
      (if neg then negate else id)
        (toInteger (nd ^. from naturalDigitsImproperIso))

instance Num DecimalDigit where
  (+) = \case
    Dec0 -> id
    Dec1 -> \case
      Dec0 -> Dec1; Dec1 -> Dec2; Dec2 -> Dec3; Dec3 -> Dec4
      Dec4 -> Dec5; Dec5 -> Dec6; Dec6 -> Dec7; Dec7 -> Dec8
      Dec8 -> Dec9; Dec9 -> Dec0
    Dec2 -> \case
      Dec0 -> Dec2; Dec1 -> Dec3; Dec2 -> Dec4; Dec3 -> Dec5
      Dec4 -> Dec6; Dec5 -> Dec7; Dec6 -> Dec8; Dec7 -> Dec9
      Dec8 -> Dec0; Dec9 -> Dec1
    Dec3 -> \case
      Dec0 -> Dec3; Dec1 -> Dec4; Dec2 -> Dec5; Dec3 -> Dec6
      Dec4 -> Dec7; Dec5 -> Dec8; Dec6 -> Dec9; Dec7 -> Dec0
      Dec8 -> Dec1; Dec9 -> Dec2
    Dec4 -> \case
      Dec0 -> Dec4; Dec1 -> Dec5; Dec2 -> Dec6; Dec3 -> Dec7
      Dec4 -> Dec8; Dec5 -> Dec9; Dec6 -> Dec0; Dec7 -> Dec1
      Dec8 -> Dec2; Dec9 -> Dec3
    Dec5 -> \case
      Dec0 -> Dec5; Dec1 -> Dec6; Dec2 -> Dec7; Dec3 -> Dec8
      Dec4 -> Dec9; Dec5 -> Dec0; Dec6 -> Dec1; Dec7 -> Dec2
      Dec8 -> Dec3; Dec9 -> Dec4
    Dec6 -> \case
      Dec0 -> Dec6; Dec1 -> Dec7; Dec2 -> Dec8; Dec3 -> Dec9
      Dec4 -> Dec0; Dec5 -> Dec1; Dec6 -> Dec2; Dec7 -> Dec3
      Dec8 -> Dec4; Dec9 -> Dec5
    Dec7 -> \case
      Dec0 -> Dec7; Dec1 -> Dec8; Dec2 -> Dec9; Dec3 -> Dec0
      Dec4 -> Dec1; Dec5 -> Dec2; Dec6 -> Dec3; Dec7 -> Dec4
      Dec8 -> Dec5; Dec9 -> Dec6
    Dec8 -> \case
      Dec0 -> Dec8; Dec1 -> Dec9; Dec2 -> Dec0; Dec3 -> Dec1
      Dec4 -> Dec2; Dec5 -> Dec3; Dec6 -> Dec4; Dec7 -> Dec5
      Dec8 -> Dec6; Dec9 -> Dec7
    Dec9 -> \case
      Dec0 -> Dec9; Dec1 -> Dec0; Dec2 -> Dec1; Dec3 -> Dec2
      Dec4 -> Dec3; Dec5 -> Dec4; Dec6 -> Dec5; Dec7 -> Dec6
      Dec8 -> Dec7; Dec9 -> Dec8
  (*) = \case
    Dec0 -> \_ -> Dec0
    Dec1 -> id
    Dec2 -> \case
      Dec0 -> Dec0; Dec1 -> Dec2; Dec2 -> Dec4; Dec3 -> Dec6
      Dec4 -> Dec8; Dec5 -> Dec0; Dec6 -> Dec2; Dec7 -> Dec4
      Dec8 -> Dec6; Dec9 -> Dec8
    Dec3 -> \case
      Dec0 -> Dec0; Dec1 -> Dec3; Dec2 -> Dec6; Dec3 -> Dec9
      Dec4 -> Dec2; Dec5 -> Dec5; Dec6 -> Dec8; Dec7 -> Dec1
      Dec8 -> Dec4; Dec9 -> Dec7
    Dec4 -> \case
      Dec0 -> Dec0; Dec1 -> Dec4; Dec2 -> Dec8; Dec3 -> Dec2
      Dec4 -> Dec6; Dec5 -> Dec0; Dec6 -> Dec4; Dec7 -> Dec8
      Dec8 -> Dec2; Dec9 -> Dec6
    Dec5 -> \case
      Dec0 -> Dec0; Dec1 -> Dec5; Dec2 -> Dec0; Dec3 -> Dec5
      Dec4 -> Dec0; Dec5 -> Dec5; Dec6 -> Dec0; Dec7 -> Dec5
      Dec8 -> Dec0; Dec9 -> Dec5
    Dec6 -> \case
      Dec0 -> Dec0; Dec1 -> Dec6; Dec2 -> Dec2; Dec3 -> Dec8
      Dec4 -> Dec4; Dec5 -> Dec0; Dec6 -> Dec6; Dec7 -> Dec2
      Dec8 -> Dec8; Dec9 -> Dec4
    Dec7 -> \case
      Dec0 -> Dec0; Dec1 -> Dec7; Dec2 -> Dec4; Dec3 -> Dec1
      Dec4 -> Dec8; Dec5 -> Dec5; Dec6 -> Dec2; Dec7 -> Dec9
      Dec8 -> Dec6; Dec9 -> Dec3
    Dec8 -> \case
      Dec0 -> Dec0; Dec1 -> Dec8; Dec2 -> Dec6; Dec3 -> Dec4
      Dec4 -> Dec2; Dec5 -> Dec0; Dec6 -> Dec8; Dec7 -> Dec6
      Dec8 -> Dec4; Dec9 -> Dec2
    Dec9 -> \case
      Dec0 -> Dec0; Dec1 -> Dec9; Dec2 -> Dec8; Dec3 -> Dec7
      Dec4 -> Dec6; Dec5 -> Dec5; Dec6 -> Dec4; Dec7 -> Dec3
      Dec8 -> Dec2; Dec9 -> Dec1
  negate = \case
    Dec0 -> Dec0; Dec1 -> Dec9; Dec2 -> Dec8; Dec3 -> Dec7
    Dec4 -> Dec6; Dec5 -> Dec5; Dec6 -> Dec4; Dec7 -> Dec3
    Dec8 -> Dec2; Dec9 -> Dec1
  abs = id
  signum = \case
    Dec0 -> Dec0
    _ -> Dec1
  fromInteger n = toEnum (fromInteger n `mod` 10)

instance Num OctalDigit where
  (+) = \case
    Oct0 -> id
    Oct1 -> \case
      Oct0 -> Oct1; Oct1 -> Oct2; Oct2 -> Oct3; Oct3 -> Oct4
      Oct4 -> Oct5; Oct5 -> Oct6; Oct6 -> Oct7; Oct7 -> Oct0
    Oct2 -> \case
      Oct0 -> Oct2; Oct1 -> Oct3; Oct2 -> Oct4; Oct3 -> Oct5
      Oct4 -> Oct6; Oct5 -> Oct7; Oct6 -> Oct0; Oct7 -> Oct1
    Oct3 -> \case
      Oct0 -> Oct3; Oct1 -> Oct4; Oct2 -> Oct5; Oct3 -> Oct6
      Oct4 -> Oct7; Oct5 -> Oct0; Oct6 -> Oct1; Oct7 -> Oct2
    Oct4 -> \case
      Oct0 -> Oct4; Oct1 -> Oct5; Oct2 -> Oct6; Oct3 -> Oct7
      Oct4 -> Oct0; Oct5 -> Oct1; Oct6 -> Oct2; Oct7 -> Oct3
    Oct5 -> \case
      Oct0 -> Oct5; Oct1 -> Oct6; Oct2 -> Oct7; Oct3 -> Oct0
      Oct4 -> Oct1; Oct5 -> Oct2; Oct6 -> Oct3; Oct7 -> Oct4
    Oct6 -> \case
      Oct0 -> Oct6; Oct1 -> Oct7; Oct2 -> Oct0; Oct3 -> Oct1
      Oct4 -> Oct2; Oct5 -> Oct3; Oct6 -> Oct4; Oct7 -> Oct5
    Oct7 -> \case
      Oct0 -> Oct7; Oct1 -> Oct0; Oct2 -> Oct1; Oct3 -> Oct2
      Oct4 -> Oct3; Oct5 -> Oct4; Oct6 -> Oct5; Oct7 -> Oct6
  (*) = \case
    Oct0 -> \_ -> Oct0
    Oct1 -> id
    Oct2 -> \case
      Oct0 -> Oct0; Oct1 -> Oct2; Oct2 -> Oct4; Oct3 -> Oct6
      Oct4 -> Oct0; Oct5 -> Oct2; Oct6 -> Oct4; Oct7 -> Oct6
    Oct3 -> \case
      Oct0 -> Oct0; Oct1 -> Oct3; Oct2 -> Oct6; Oct3 -> Oct1
      Oct4 -> Oct4; Oct5 -> Oct7; Oct6 -> Oct2; Oct7 -> Oct5
    Oct4 -> \case
      Oct0 -> Oct0; Oct1 -> Oct4; Oct2 -> Oct0; Oct3 -> Oct4
      Oct4 -> Oct0; Oct5 -> Oct4; Oct6 -> Oct0; Oct7 -> Oct4
    Oct5 -> \case
      Oct0 -> Oct0; Oct1 -> Oct5; Oct2 -> Oct2; Oct3 -> Oct7
      Oct4 -> Oct4; Oct5 -> Oct1; Oct6 -> Oct6; Oct7 -> Oct3
    Oct6 -> \case
      Oct0 -> Oct0; Oct1 -> Oct6; Oct2 -> Oct4; Oct3 -> Oct2
      Oct4 -> Oct0; Oct5 -> Oct6; Oct6 -> Oct4; Oct7 -> Oct2
    Oct7 -> \case
      Oct0 -> Oct0; Oct1 -> Oct7; Oct2 -> Oct6; Oct3 -> Oct5
      Oct4 -> Oct4; Oct5 -> Oct3; Oct6 -> Oct2; Oct7 -> Oct1
  negate = \case
    Oct0 -> Oct0; Oct1 -> Oct7; Oct2 -> Oct6; Oct3 -> Oct5
    Oct4 -> Oct4; Oct5 -> Oct3; Oct6 -> Oct2; Oct7 -> Oct1
  abs = id
  signum = \case
    Oct0 -> Oct0
    _ -> Oct1
  fromInteger n = toEnum (fromInteger n `mod` 8)

instance Num HexDigit where
  (+) = \case
    Hex0 -> id
    Hex1 -> \case
      Hex0 -> Hex1; Hex1 -> Hex2; Hex2 -> Hex3; Hex3 -> Hex4
      Hex4 -> Hex5; Hex5 -> Hex6; Hex6 -> Hex7; Hex7 -> Hex8
      Hex8 -> Hex9; Hex9 -> HexA; HexA -> HexB; HexB -> HexC
      HexC -> HexD; HexD -> HexE; HexE -> HexF; HexF -> Hex0
    Hex2 -> \case
      Hex0 -> Hex2; Hex1 -> Hex3; Hex2 -> Hex4; Hex3 -> Hex5
      Hex4 -> Hex6; Hex5 -> Hex7; Hex6 -> Hex8; Hex7 -> Hex9
      Hex8 -> HexA; Hex9 -> HexB; HexA -> HexC; HexB -> HexD
      HexC -> HexE; HexD -> HexF; HexE -> Hex0; HexF -> Hex1
    Hex3 -> \case
      Hex0 -> Hex3; Hex1 -> Hex4; Hex2 -> Hex5; Hex3 -> Hex6
      Hex4 -> Hex7; Hex5 -> Hex8; Hex6 -> Hex9; Hex7 -> HexA
      Hex8 -> HexB; Hex9 -> HexC; HexA -> HexD; HexB -> HexE
      HexC -> HexF; HexD -> Hex0; HexE -> Hex1; HexF -> Hex2
    Hex4 -> \case
      Hex0 -> Hex4; Hex1 -> Hex5; Hex2 -> Hex6; Hex3 -> Hex7
      Hex4 -> Hex8; Hex5 -> Hex9; Hex6 -> HexA; Hex7 -> HexB
      Hex8 -> HexC; Hex9 -> HexD; HexA -> HexE; HexB -> HexF
      HexC -> Hex0; HexD -> Hex1; HexE -> Hex2; HexF -> Hex3
    Hex5 -> \case
      Hex0 -> Hex5; Hex1 -> Hex6; Hex2 -> Hex7; Hex3 -> Hex8
      Hex4 -> Hex9; Hex5 -> HexA; Hex6 -> HexB; Hex7 -> HexC
      Hex8 -> HexD; Hex9 -> HexE; HexA -> HexF; HexB -> Hex0
      HexC -> Hex1; HexD -> Hex2; HexE -> Hex3; HexF -> Hex4
    Hex6 -> \case
      Hex0 -> Hex6; Hex1 -> Hex7; Hex2 -> Hex8; Hex3 -> Hex9
      Hex4 -> HexA; Hex5 -> HexB; Hex6 -> HexC; Hex7 -> HexD
      Hex8 -> HexE; Hex9 -> HexF; HexA -> Hex0; HexB -> Hex1
      HexC -> Hex2; HexD -> Hex3; HexE -> Hex4; HexF -> Hex5
    Hex7 -> \case
      Hex0 -> Hex7; Hex1 -> Hex8; Hex2 -> Hex9; Hex3 -> HexA
      Hex4 -> HexB; Hex5 -> HexC; Hex6 -> HexD; Hex7 -> HexE
      Hex8 -> HexF; Hex9 -> Hex0; HexA -> Hex1; HexB -> Hex2
      HexC -> Hex3; HexD -> Hex4; HexE -> Hex5; HexF -> Hex6
    Hex8 -> \case
      Hex0 -> Hex8; Hex1 -> Hex9; Hex2 -> HexA; Hex3 -> HexB
      Hex4 -> HexC; Hex5 -> HexD; Hex6 -> HexE; Hex7 -> HexF
      Hex8 -> Hex0; Hex9 -> Hex1; HexA -> Hex2; HexB -> Hex3
      HexC -> Hex4; HexD -> Hex5; HexE -> Hex6; HexF -> Hex7
    Hex9 -> \case
      Hex0 -> Hex9; Hex1 -> HexA; Hex2 -> HexB; Hex3 -> HexC
      Hex4 -> HexD; Hex5 -> HexE; Hex6 -> HexF; Hex7 -> Hex0
      Hex8 -> Hex1; Hex9 -> Hex2; HexA -> Hex3; HexB -> Hex4
      HexC -> Hex5; HexD -> Hex6; HexE -> Hex7; HexF -> Hex8
    HexA -> \case
      Hex0 -> HexA; Hex1 -> HexB; Hex2 -> HexC; Hex3 -> HexD
      Hex4 -> HexE; Hex5 -> HexF; Hex6 -> Hex0; Hex7 -> Hex1
      Hex8 -> Hex2; Hex9 -> Hex3; HexA -> Hex4; HexB -> Hex5
      HexC -> Hex6; HexD -> Hex7; HexE -> Hex8; HexF -> Hex9
    HexB -> \case
      Hex0 -> HexB; Hex1 -> HexC; Hex2 -> HexD; Hex3 -> HexE
      Hex4 -> HexF; Hex5 -> Hex0; Hex6 -> Hex1; Hex7 -> Hex2
      Hex8 -> Hex3; Hex9 -> Hex4; HexA -> Hex5; HexB -> Hex6
      HexC -> Hex7; HexD -> Hex8; HexE -> Hex9; HexF -> HexA
    HexC -> \case
      Hex0 -> HexC; Hex1 -> HexD; Hex2 -> HexE; Hex3 -> HexF
      Hex4 -> Hex0; Hex5 -> Hex1; Hex6 -> Hex2; Hex7 -> Hex3
      Hex8 -> Hex4; Hex9 -> Hex5; HexA -> Hex6; HexB -> Hex7
      HexC -> Hex8; HexD -> Hex9; HexE -> HexA; HexF -> HexB
    HexD -> \case
      Hex0 -> HexD; Hex1 -> HexE; Hex2 -> HexF; Hex3 -> Hex0
      Hex4 -> Hex1; Hex5 -> Hex2; Hex6 -> Hex3; Hex7 -> Hex4
      Hex8 -> Hex5; Hex9 -> Hex6; HexA -> Hex7; HexB -> Hex8
      HexC -> Hex9; HexD -> HexA; HexE -> HexB; HexF -> HexC
    HexE -> \case
      Hex0 -> HexE; Hex1 -> HexF; Hex2 -> Hex0; Hex3 -> Hex1
      Hex4 -> Hex2; Hex5 -> Hex3; Hex6 -> Hex4; Hex7 -> Hex5
      Hex8 -> Hex6; Hex9 -> Hex7; HexA -> Hex8; HexB -> Hex9
      HexC -> HexA; HexD -> HexB; HexE -> HexC; HexF -> HexD
    HexF -> \case
      Hex0 -> HexF; Hex1 -> Hex0; Hex2 -> Hex1; Hex3 -> Hex2
      Hex4 -> Hex3; Hex5 -> Hex4; Hex6 -> Hex5; Hex7 -> Hex6
      Hex8 -> Hex7; Hex9 -> Hex8; HexA -> Hex9; HexB -> HexA
      HexC -> HexB; HexD -> HexC; HexE -> HexD; HexF -> HexE
  (*) = \case
    Hex0 -> \_ -> Hex0
    Hex1 -> id
    Hex2 -> \case
      Hex0 -> Hex0; Hex1 -> Hex2; Hex2 -> Hex4; Hex3 -> Hex6
      Hex4 -> Hex8; Hex5 -> HexA; Hex6 -> HexC; Hex7 -> HexE
      Hex8 -> Hex0; Hex9 -> Hex2; HexA -> Hex4; HexB -> Hex6
      HexC -> Hex8; HexD -> HexA; HexE -> HexC; HexF -> HexE
    Hex3 -> \case
      Hex0 -> Hex0; Hex1 -> Hex3; Hex2 -> Hex6; Hex3 -> Hex9
      Hex4 -> HexC; Hex5 -> HexF; Hex6 -> Hex2; Hex7 -> Hex5
      Hex8 -> Hex8; Hex9 -> HexB; HexA -> HexE; HexB -> Hex1
      HexC -> Hex4; HexD -> Hex7; HexE -> HexA; HexF -> HexD
    Hex4 -> \case
      Hex0 -> Hex0; Hex1 -> Hex4; Hex2 -> Hex8; Hex3 -> HexC
      Hex4 -> Hex0; Hex5 -> Hex4; Hex6 -> Hex8; Hex7 -> HexC
      Hex8 -> Hex0; Hex9 -> Hex4; HexA -> Hex8; HexB -> HexC
      HexC -> Hex0; HexD -> Hex4; HexE -> Hex8; HexF -> HexC
    Hex5 -> \case
      Hex0 -> Hex0; Hex1 -> Hex5; Hex2 -> HexA; Hex3 -> HexF
      Hex4 -> Hex4; Hex5 -> Hex9; Hex6 -> HexE; Hex7 -> Hex3
      Hex8 -> Hex8; Hex9 -> HexD; HexA -> Hex2; HexB -> Hex7
      HexC -> HexC; HexD -> Hex1; HexE -> Hex6; HexF -> HexB
    Hex6 -> \case
      Hex0 -> Hex0; Hex1 -> Hex6; Hex2 -> HexC; Hex3 -> Hex2
      Hex4 -> Hex8; Hex5 -> HexE; Hex6 -> Hex4; Hex7 -> HexA
      Hex8 -> Hex0; Hex9 -> Hex6; HexA -> HexC; HexB -> Hex2
      HexC -> Hex8; HexD -> HexE; HexE -> Hex4; HexF -> HexA
    Hex7 -> \case
      Hex0 -> Hex0; Hex1 -> Hex7; Hex2 -> HexE; Hex3 -> Hex5
      Hex4 -> HexC; Hex5 -> Hex3; Hex6 -> HexA; Hex7 -> Hex1
      Hex8 -> Hex8; Hex9 -> HexF; HexA -> Hex6; HexB -> HexD
      HexC -> Hex4; HexD -> HexB; HexE -> Hex2; HexF -> Hex9
    Hex8 -> \case
      Hex0 -> Hex0; Hex1 -> Hex8; Hex2 -> Hex0; Hex3 -> Hex8
      Hex4 -> Hex0; Hex5 -> Hex8; Hex6 -> Hex0; Hex7 -> Hex8
      Hex8 -> Hex0; Hex9 -> Hex8; HexA -> Hex0; HexB -> Hex8
      HexC -> Hex0; HexD -> Hex8; HexE -> Hex0; HexF -> Hex8
    Hex9 -> \case
      Hex0 -> Hex0; Hex1 -> Hex9; Hex2 -> Hex2; Hex3 -> HexB
      Hex4 -> Hex4; Hex5 -> HexD; Hex6 -> Hex6; Hex7 -> HexF
      Hex8 -> Hex8; Hex9 -> Hex1; HexA -> HexA; HexB -> Hex3
      HexC -> HexC; HexD -> Hex5; HexE -> HexE; HexF -> Hex7
    HexA -> \case
      Hex0 -> Hex0; Hex1 -> HexA; Hex2 -> Hex4; Hex3 -> HexE
      Hex4 -> Hex8; Hex5 -> Hex2; Hex6 -> HexC; Hex7 -> Hex6
      Hex8 -> Hex0; Hex9 -> HexA; HexA -> Hex4; HexB -> HexE
      HexC -> Hex8; HexD -> Hex2; HexE -> HexC; HexF -> Hex6
    HexB -> \case
      Hex0 -> Hex0; Hex1 -> HexB; Hex2 -> Hex6; Hex3 -> Hex1
      Hex4 -> HexC; Hex5 -> Hex7; Hex6 -> Hex2; Hex7 -> HexD
      Hex8 -> Hex8; Hex9 -> Hex3; HexA -> HexE; HexB -> Hex9
      HexC -> Hex4; HexD -> HexF; HexE -> HexA; HexF -> Hex5
    HexC -> \case
      Hex0 -> Hex0; Hex1 -> HexC; Hex2 -> Hex8; Hex3 -> Hex4
      Hex4 -> Hex0; Hex5 -> HexC; Hex6 -> Hex8; Hex7 -> Hex4
      Hex8 -> Hex0; Hex9 -> HexC; HexA -> Hex8; HexB -> Hex4
      HexC -> Hex0; HexD -> HexC; HexE -> Hex8; HexF -> Hex4
    HexD -> \case
      Hex0 -> Hex0; Hex1 -> HexD; Hex2 -> HexA; Hex3 -> Hex7
      Hex4 -> Hex4; Hex5 -> Hex1; Hex6 -> HexE; Hex7 -> HexB
      Hex8 -> Hex8; Hex9 -> Hex5; HexA -> Hex2; HexB -> HexF
      HexC -> HexC; HexD -> Hex9; HexE -> Hex6; HexF -> Hex3
    HexE -> \case
      Hex0 -> Hex0; Hex1 -> HexE; Hex2 -> HexC; Hex3 -> HexA
      Hex4 -> Hex8; Hex5 -> Hex6; Hex6 -> Hex4; Hex7 -> Hex2
      Hex8 -> Hex0; Hex9 -> HexE; HexA -> HexC; HexB -> HexA
      HexC -> Hex8; HexD -> Hex6; HexE -> Hex4; HexF -> Hex2
    HexF -> \case
      Hex0 -> Hex0; Hex1 -> HexF; Hex2 -> HexE; Hex3 -> HexD
      Hex4 -> HexC; Hex5 -> HexB; Hex6 -> HexA; Hex7 -> Hex9
      Hex8 -> Hex8; Hex9 -> Hex7; HexA -> Hex6; HexB -> Hex5
      HexC -> Hex4; HexD -> Hex3; HexE -> Hex2; HexF -> Hex1
  negate = \case
    Hex0 -> Hex0; Hex1 -> HexF; Hex2 -> HexE; Hex3 -> HexD
    Hex4 -> HexC; Hex5 -> HexB; Hex6 -> HexA; Hex7 -> Hex9
    Hex8 -> Hex8; Hex9 -> Hex7; HexA -> Hex6; HexB -> Hex5
    HexC -> Hex4; HexD -> Hex3; HexE -> Hex2; HexF -> Hex1
  abs = id
  signum = \case
    Hex0 -> Hex0
    _ -> Hex1
  fromInteger n = toEnum (fromInteger n `mod` 16)
