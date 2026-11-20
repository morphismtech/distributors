module Properties.Disjunctive (disjunctiveProperties) where

import Data.Functor.Contravariant (Predicate (..))
import Data.Int (Int8)
import Data.Monoid (Ap (..))
import Data.Monoid.Disjunctive
import Data.Word (Word8)
import Numeric.Natural (Natural)
import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck
import Text.ParserCombinators.ReadP (ReadP, readP_to_S, string)

disjunctiveProperties :: Spec
disjunctiveProperties = do
  describe "Bits, as a BooleanAlgebra of bit vectors" $ do
    booleanLaws "Int" (arbitrary :: Gen Int)
    booleanLaws "Int8" (arbitrary :: Gen Int8)
    booleanLaws "Word8" (arbitrary :: Gen Word8)
    booleanLaws "Integer" (arbitrary :: Gen Integer)
    prop "Natural disjoins as a monoid" $ \(NonNegative (x :: Integer)) y ->
      let n = fromInteger x :: Natural
          m = fromInteger (getNonNegative y) :: Natural
      in (falseP >|< n) === n .&&. (n >|< m) === (m >|< n)
  describe "Predicate, as a Kleene algebra" $
    prop "its star is true" $ \(Fun _ p) (x :: Int) ->
      getPredicate (starK (Predicate p)) x === True
        .&&. getPredicate (optK (Predicate p)) x === True
  describe "Ap, as a Kleene algebra of languages" $
    it "stars by many, concatenated" $ do
      let star = getAp (starK (Ap (string "ab"))) :: ReadP String
      [w | (w, "") <- readP_to_S star "ababab"] `shouldBe` ["ababab"]
      [w | (w, "") <- readP_to_S star ""] `shouldBe` [""]
      let plus = getAp (plusK (Ap (string "ab"))) :: ReadP String
      [w | (w, "") <- readP_to_S plus ""] `shouldBe` []

booleanLaws
  :: (Show b, Eq b, BooleanAlgebra b) => String -> Gen b -> Spec
booleanLaws name gen = describe name $ do
  prop "x >&< notP x = falseP & x >|< notP x = trueP" $
    forAll gen $ \x ->
      (x >&< notP x) === falseP .&&. (x >|< notP x) === trueP
  prop "de Morgan" $ forAll gen $ \x -> forAll gen $ \y ->
    notP (x >|< y) === (notP x >&< notP y)
  prop "notP . notP = id" $ forAll gen $ \x -> notP (notP x) === x
  prop "units" $ forAll gen $ \x ->
    (x >|< falseP) === x .&&. (x >&< trueP) === x
