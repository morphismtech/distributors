module Properties.Base (baseProperties) where

import Control.Lens.Grammar
import Data.Int (Int8)
import GHC.Exts (toList)
import Data.Word (Word8)
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

-- | Printing then parsing round-trips, compared by @eq@.
roundTrips :: forall a. (CtxGrammar Char a, Show a) => a -> Property
roundTrips a = case printed a of
  Nothing -> counterexample ("doesn't print: " <> show a) False
  Just str -> map show (parsed @a str) === [show a]

baseProperties :: Spec
baseProperties = do
  describe "round trips, printing then parsing" $ do
    prop "Char" $ roundTrips @Char
    prop "String" $ roundTrips @String
    prop "Natural" $ \(NonNegative (n :: Integer)) -> roundTrips (fromInteger n :: Natural)
    prop "Integer" $ roundTrips @Integer
    prop "Int" $ roundTrips @Int
    prop "Int8" $ roundTrips @Int8
    prop "Word8" $ roundTrips @Word8
    prop "Double" $ roundTrips @Double
    prop "Float" $ roundTrips @Float
    it "Double's NaN, infinities & negative zero" $
      mapM_ (\x -> map show (parsed @Double =<< maybe [] pure (printed x)) `shouldBe` [show x])
        [0 / 0, 1 / 0, -(1 / 0), -0.0 :: Double]
  describe "parsing more than printing, by improper isos" $ do
    it "Natural, with leading zeros" $ parsed @Natural "007" `shouldBe` [7]
    it "Integer, -0" $ parsed @Integer "-0" `shouldBe` [0]
    it "Double, exponents & fractions" $ do
      parsed @Double "1E+5" `shouldBe` [100000]
      parsed @Double "1.50" `shouldBe` [1.5]
      parsed @Double "2e-1" `shouldBe` [0.2]
    it "prints canonically" $ do
      printed (7 :: Natural) `shouldBe` Just "7"
      printed (1.5 :: Double) `shouldBe` Just "1.5"
  describe "sized integers, failing out of range" $ do
    it "Word8" $ do
      parsed @Word8 "255" `shouldBe` [255]
      parsed @Word8 "256" `shouldBe` []
      parsed @Word8 "-1" `shouldBe` []
    it "Int8" $ do
      parsed @Int8 "-128" `shouldBe` [-128]
      parsed @Int8 "128" `shouldBe` []
  describe "statically LL(1), by ll1Conflicts" $ do
    it "Char" $ ll1Conflicts (regbnfG @Char Char) `shouldBe` []
    it "String" $ ll1Conflicts (regbnfG @Char String) `shouldBe` []
    it "Natural" $ ll1Conflicts (regbnfG @Char Natural) `shouldBe` []
    it "Integer" $ ll1Conflicts (regbnfG @Char Integer) `shouldBe` []
    it "Double" $ ll1Conflicts (regbnfG @Char Double) `shouldBe` []
  describe "regular expressions" $ do
    it "Natural" $ toList (regexG @Char Natural) `shouldBe` "[0123456789]+"
    it "Integer" $ toList (regexG @Char Integer) `shouldBe` "-?[0123456789]+"
