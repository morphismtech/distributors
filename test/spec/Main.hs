module Main (main) where

import Data.Foldable hiding (toList)
import Control.Lens.Grammar
import GHC.Exts
import Test.Hspec

import Examples.RegString
import Examples.Arithmetic
import Examples.Json
import Examples.SExpr
import Examples.Lambda

main :: IO ()
main = hspec $ do
  describe "regexGrammar" $
    for_ regexExamples $ \(rex, str) -> do
      it ("should print " <> show (runRegString rex) <> " correctly") $
        toList rex `shouldBe` str
      it ("should parse " <> str <> " correctly") $ do
        fromString str `shouldBe` rex

  -- testGrammar "regexGrammar" regexGrammar regexExamples
  testGrammar "arithGrammar" arithGrammar arithExamples
  testGrammar "jsonGrammar" jsonGrammar jsonExamples
  testGrammar "sexprGrammar" sexprGrammar sexprExamples
  testGrammar "lambdaGrammar" lambdaGrammar lambdaExamples

testGrammar :: (Show a, Eq a) => String -> Grammar Char a -> [(a, String)] -> Spec
testGrammar name grammar examples =
  describe name $
    for_ examples $ \(expectedSyntax, expectedString) -> do
      it ("should parse from " <> expectedString <> " correctly") $ do
        let actualSyntax = [parsed | (parsed, "") <- parseG grammar expectedString]
        actualSyntax `shouldBe` [expectedSyntax]
      it ("should unparse to " <> expectedString <> " correctly") $ do
        let actualString = unparseG grammar expectedSyntax ""
        actualString `shouldBe` Just expectedString
      it ("should print to " <> expectedString <> " correctly") $ do
        let actualString = ($ "") <$> printG grammar expectedSyntax
        actualString `shouldBe` Just expectedString
