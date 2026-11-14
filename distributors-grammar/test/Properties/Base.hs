module Properties.Base (baseProperties) where

import Control.Lens.Grammar
import Data.Int (Int8, Int64)
import Data.Word (Word8, Word64)
import Numeric.Natural (Natural)
import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck

-- | Parse all of a string, if it parses.
parsed :: forall a. CtxGrammar Char a => String -> [a]
parsed str = [a | (a, "") <- parseG @a str]

-- | Print a value, if it prints.
printed :: CtxGrammar Char a => a -> Maybe String
printed a = ($ "") <$> printG a

-- | Printing is `show`, & parsing its print is the value, by `show`,
-- so that @NaN@ is itself.
showParity :: forall a. (CtxGrammar Char a, Show a) => a -> Property
showParity a =
  printed a === Just (show a) .&&. map show (parsed @a (show a)) === [show a]

-- | Parsing is `read`, for strings which `read` parses.
readParity :: forall a. (CtxGrammar Char a, Read a, Show a) => String -> Expectation
readParity str = map show (parsed @a str) `shouldBe` [show (read str :: a)]

-- | Parsing fails, as `read` does.
readFails :: forall a. (CtxGrammar Char a, Show a) => String -> Expectation
readFails str = map show (parsed @a str) `shouldBe` []

baseProperties :: Spec
baseProperties = do
  describe "prints as show does, & parses its print" $ do
    prop "Char" $ showParity @Char
    prop "Natural" $ \(NonNegative (n :: Integer)) -> showParity (fromInteger n :: Natural)
    prop "Integer" $ showParity @Integer
    prop "Int" $ showParity @Int
    prop "Int8" $ showParity @Int8
    prop "Int64" $ showParity @Int64
    prop "Word8" $ showParity @Word8
    prop "Word64" $ showParity @Word64
    prop "Double" $ showParity @Double
    prop "Float" $ showParity @Float
    it "Double's & Float's specials" $
      conjoin (map (showParity @Double) [0 / 0, 1 / 0, -(1 / 0), -0.0, 0, 0.1, 1.0e7, 9999999, 5.0e-324])
        .&&. conjoin (map (showParity @Float) [0 / 0, 1 / 0, -0.0, 1.0e-2, 1.0e7])
    it "Char's escapes" $
      conjoin $ map (showParity @Char) (['\0' .. '\DEL'] <> ['\128', '\1234', '\1114111'])
  describe "parses as read does" $ do
    it "Natural" $ mapM_ (readParity @Natural) ["007", "0x1F", "0X1f", "0o17", "0O17", "0b101", "-0", "-0x00"]
    it "Integer" $ mapM_ (readParity @Integer) ["-0", "-12", "0x1F", "-0o17", "0b0"]
    it "sized integers, wrapping" $ do
      mapM_ (readParity @Word8) ["255", "256", "-1", "0x1FF"]
      mapM_ (readParity @Int8) ["127", "128", "-129"]
    it "Double" $ mapM_ (readParity @Double)
      [ "1E+5", "1.50", "2e-1", "0x10", "-Infinity", "Infinity", "NaN", "-NaN"
      , "1e400", "1e-400", "0.000e99999999", "007.5", "1e-0" ]
    it "Char" $ mapM_ (readParity @Char)
      [ "'a'", "'\\n'", "'\\SOH'", "'\\SO'", "'\\1234'", "'\\x41'", "'\\X41'"
      , "'\\o101'", "'\\^A'", "'\\^@'", "'\\DEL'", "'\"'", "'\\\"'", "'\\''"
      , "'\\SP'", "'\\BEL'", "'\\a'", "'\n'" ]
  describe "fails as read does" $ do
    it "Natural" $ mapM_ (readFails @Natural) ["-1", "-0x1"]
    it "Integer" $ mapM_ (readFails @Integer) ["1.5", "1e3", "0x", "--1", "+1"]
    it "Char" $ mapM_ (readFails @Char) ["'''", "'\\&'", "'ab'", "''", "'\\q'"]
  describe "statically LL(1), by ll1Conflicts" $ do
    it "Char" $ ll1Conflicts (regbnfG @Char Char) `shouldBe` []
    it "Natural" $ ll1Conflicts (regbnfG @Char Natural) `shouldBe` []
    it "Integer" $ ll1Conflicts (regbnfG @Char Integer) `shouldBe` []
    it "Double" $ ll1Conflicts (regbnfG @Char Double) `shouldBe` []
