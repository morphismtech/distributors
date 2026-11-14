module Properties.Base (baseProperties, readShowEquivalence) where

import Control.Lens.Grammar
import Data.Char (intToDigit, isAscii, isControl, isSpace, ord, toUpper)
import Data.Int (Int8, Int16, Int32, Int64)
import Data.Foldable (for_)
import Control.Monad ((>=>))
import Data.List (intercalate, sort)
import Data.Word (Word8, Word16, Word32, Word64)
import GHC.Generics (Generic)
import Numeric (showHex, showIntAtBase, showOct)
import Numeric.Natural (Natural)
import Test.Hspec
import Test.Hspec.QuickCheck (modifyMaxSuccess, prop)
import Test.QuickCheck

{- | Equivalence with a type's stock `Read` & `Show` instances, at each
precedence: showing is `showsPrec`, & reading is `readsPrec`, all of a
string but whitespace, for strings of its values, by its lexical variants,
decorated by whitespace & parentheses, & mutated, so that strings which
`read` rejects are tried too. Each new instance runs it.
-}
readShowEquivalence
  :: forall a. (PrecGrammar a, Read a, Show a)
  => String -> Gen a -> (a -> Gen String) -> Spec
readShowEquivalence name values variants = describe name $
  for_ [0, 6, 7, 11] $ \d -> describe ("at precedence " <> show d) $ do
    prop "shows as showsPrec does" $ forAll values $ \a ->
      (($ "") <$> showsPrecG d a) === Just (showsPrec d a "")
    modifyMaxSuccess (const 1000) $ prop "reads as readsPrec does" $
      forAll (values >>= variants >>= decorated >>= mutated) $ \str ->
        complete (readsPrecG @a d str) === complete (readsPrec @a d str)
  where
    complete parses = sort [show a | (a, rest) <- parses, all isSpace rest]

-- | Whitespace, `isSpace` & not, often none.
spaces :: Gen String
spaces = frequency
  [ (3, pure "")
  , (1, listOf1 (elements " \t\n\v\f\r\xa0\x2003\x3000"))
  , (1, pure "\x2028") ]

-- | Within any parentheses, amid whitespace.
decorated :: String -> Gen String
decorated str = do
  depth <- frequency [(4, pure 0), (2, pure 1), (1, pure 2)]
  go depth
  where
    spaced s = do
      lead <- spaces
      trail <- spaces
      pure (lead <> s <> trail)
    go :: Int -> Gen String
    go 0 = spaced str
    go n = go (n - 1) >>= \s -> spaced ("(" <> s <> ")")

-- | Edited, once or twice, or not.
mutated :: String -> Gen String
mutated str = frequency [(2, pure str), (1, edit str), (1, edit str >>= edit)]
  where
    edit s = do
      i <- choose (0, length s)
      c <- elements "0123456789aefxXoObBeE+-.()' \\\"^NSOHDL\x2028"
      let (front, back) = splitAt i s
      elements
        [ front <> [c] <> back
        , front <> drop 1 back
        , front <> [c] <> drop 1 back ]

-- | An integer's strings: decimal or based, with leading zeros, & signed.
integral :: Integral a => a -> Gen String
integral x = do
  let n = toInteger x
  magnitude <- oneof
    [ pure (show (abs n))
    , (<> show (abs n)) <$> zeros
    , do
        (prefix, base) <- elements [("b", 2), ("o", 8), ("x", 16)]
        upper <- arbitrary
        digits <- (<> showIntAtBase base intToDigit (abs n) "") <$> zeros
        let cased = if upper then map toUpper else id
        pure ("0" <> cased prefix <> cased digits) ]
  sign <- if n < 0 then pure True else frequency [(5, pure False), (1, pure True)]
  gap <- spaces
  pure (if sign then "-" <> gap <> magnitude else magnitude)
  where
    zeros = flip replicate '0' <$> choose (0, 2)

-- | A floating point number's strings: shown, with its exponent's `E` &
-- @+@, & zeros, or as an integer.
floating :: (RealFloat a, Show a) => a -> Gen String
floating x = oneof
  [ pure (show x)
  , pure (map (\c -> if c == 'e' then 'E' else c) (show x))
  , pure (concatMap (\c -> if c == 'e' then "e+" else [c]) (show x))
  , pure ("0" <> show x)
  , pure (show x <> "0")
  , integral (truncate x :: Integer) ]

-- | A character's literals: shown, raw, or by a code, in any base.
character :: Char -> Gen String
character c = do
  escape <- oneof $
    [ pure (drop 1 (init (show c))) ]
    <> [pure [c] | c `notElem` "\\'"]
    <> [ pure ("\\" <> show (ord c))
       , pure ("\\o" <> showOct (ord c) "")
       , pure ("\\x" <> showHex (ord c) "")
       , pure ("\\X" <> map toUpper (showHex (ord c) "")) ]
    <> [pure ['\\', '^', toEnum (ord c + 64)] | ord c < 32]
  pure ("'" <> escape <> "'")

-- | A list's strings: in brackets, its items' variants, amid whitespace.
listing :: (a -> Gen String) -> [a] -> Gen String
listing itemVariant xs = do
  items <- traverse (itemVariant >=> decorated) xs
  pure ("[" <> intercalate "," items <> "]")

-- | A string's literals: shown, by its characters' escapes, with empty
-- escapes & gaps, or listed, as characters.
string :: String -> Gen String
string s = oneof [pure (show s), literal, listing character s]
  where
    literal = do
      parts <- traverse piece s
      pure ("\"" <> concat parts <> "\"")
    piece c = do
      lead <- frequency [(8, pure ""), (1, pure "\\&"), (1, pure "\\ \n\\")]
      escape <- oneof $
        [pure (drop 1 (init (show [c])))]
        <> [pure [c] | c `notElem` "\\\""]
        <> [ pure ("\\" <> show (ord c))
           , pure ("\\o" <> showOct (ord c) "")
           , pure ("\\x" <> showHex (ord c) "") ]
      pure (lead <> escape)

-- | A value's strings, shown, at precedence 0 or 11, its lexemes rejoined
-- by whitespace, or none, by `lex`.
relexed :: Show a => a -> Gen String
relexed x = do
  shown <- elements [show x, showsPrec 11 x ""]
  oneof [pure shown, rejoin (lexemes shown)]
  where
    lexemes str = case lex str of
      [(lexeme, rest)] | not (null lexeme) -> lexeme : lexemes rest
      _ -> []
    rejoin = fmap concat . traverse (\lexeme -> (lexeme <>) <$> gap)
    gap = frequency [(2, pure ""), (2, pure " "), (1, spaces)]

-- | A type of each shape of constructor, deriving `Read` & `Show`.
data Shapes
  = Nullary
  | Prefixed Int Bool
  | Record {field :: Int, other :: Maybe Char}
  | Operators {(+++) :: Integer}
  | Int :+: Integer
  | Int `Named` Bool
  | (:%) Int Int
  deriving stock (Eq, Show, Read, Generic)
infixl 6 :+:
infix 4 `Named`
instance PrecGrammar Shapes
instance Arbitrary Shapes where
  arbitrary = oneof
    [ pure Nullary
    , Prefixed <$> arbitrary <*> arbitrary
    , Record <$> arbitrary <*> arbitrary
    , Operators <$> arbitrary
    , (:+:) <$> arbitrary <*> arbitrary
    , Named <$> arbitrary <*> arbitrary
    , (:%) <$> arbitrary <*> arbitrary ]

characters :: Gen Char
characters = frequency
  [ (3, arbitraryASCIIChar)
  , (2, elements "\\'\"\SO\SOH\DEL\NUL ")
  , (1, arbitrary `suchThat` (\c -> isControl c || not (isAscii c)))
  , (1, arbitraryUnicodeChar) ]

-- | Including the special values.
floats :: (Arbitrary a, RealFloat a) => Gen a
floats = frequency
  [ (6, arbitrary)
  , (1, elements [0 / 0, 1 / 0, -(1 / 0), -0.0, 0, 0.1, 1.0e7, 9999999]) ]

baseProperties :: Spec
baseProperties = describe "equivalent to Read & Show" $ do
  readShowEquivalence "Char" characters character
  readShowEquivalence "Natural"
    (fromInteger . getNonNegative <$> arbitrary :: Gen Natural) integral
  readShowEquivalence "Integer" (arbitrary :: Gen Integer) integral
  readShowEquivalence "Int" (arbitrary :: Gen Int) integral
  readShowEquivalence "Int8" (arbitrary :: Gen Int8) integral
  readShowEquivalence "Int16" (arbitrary :: Gen Int16) integral
  readShowEquivalence "Int32" (arbitrary :: Gen Int32) integral
  readShowEquivalence "Int64" (arbitrary :: Gen Int64) integral
  readShowEquivalence "Word" (arbitrary :: Gen Word) integral
  readShowEquivalence "Word8" (arbitrary :: Gen Word8) integral
  readShowEquivalence "Word16" (arbitrary :: Gen Word16) integral
  readShowEquivalence "Word32" (arbitrary :: Gen Word32) integral
  readShowEquivalence "Word64" (arbitrary :: Gen Word64) integral
  readShowEquivalence "Double" (floats :: Gen Double) floating
  readShowEquivalence "Float" (floats :: Gen Float) floating
  readShowEquivalence "String" (listOf characters) string
  readShowEquivalence "[Int]" (arbitrary :: Gen [Int]) (listing integral)
  readShowEquivalence "[[Integer]]" (arbitrary :: Gen [[Integer]]) (listing (listing integral))
  readShowEquivalence "Bool" (arbitrary :: Gen Bool) relexed
  readShowEquivalence "Ordering" (arbitrary :: Gen Ordering) relexed
  readShowEquivalence "()" (arbitrary :: Gen ()) relexed
  readShowEquivalence "Maybe Int" (arbitrary :: Gen (Maybe Int)) relexed
  readShowEquivalence "Either Int Bool" (arbitrary :: Gen (Either Int Bool)) relexed
  readShowEquivalence "(Int, Bool)" (arbitrary :: Gen (Int, Bool)) relexed
  readShowEquivalence "(Char, String, Integer)" (arbitrary :: Gen (Char, String, Integer)) relexed
  readShowEquivalence "[Maybe (Either Bool Integer)]"
    (arbitrary :: Gen [Maybe (Either Bool Integer)]) relexed
  readShowEquivalence "Maybe (Maybe Double)" (arbitrary :: Gen (Maybe (Maybe Double))) relexed
  readShowEquivalence "Shapes" (arbitrary :: Gen Shapes) relexed
  readShowEquivalence "Maybe Shapes" (arbitrary :: Gen (Maybe Shapes)) relexed
