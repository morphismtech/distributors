module Main (main) where

import Data.Foldable hiding (toList)
import Data.Maybe (listToMaybe)
import Control.Lens.Grammar
import Test.Hspec

import Examples.RegString
import Examples.Arithmetic
import Examples.Json
import Examples.SExpr
import Examples.Lambda
import Examples.LenVec
import Examples.SemVer

main :: IO ()
main = hspec $ do
  testGrammar "regexGrammar" regexGrammar regexExamples
  testGrammar "semverGrammar" semverGrammar semverExamples
  testGrammar "arithGrammar" arithGrammar arithExamples
  testGrammar "jsonGrammar" jsonGrammar jsonExamples
  testGrammar "sexprGrammar" sexprGrammar sexprExamples
  testGrammar "lambdaGrammar" lambdaGrammar lambdaExamples
  testGrammar "lenvecGrammar" lenvecGrammar lenvecExamples

testGrammar :: (Show a, Eq a) => String -> CtxGrammar Char a -> [(a, String)] -> Spec
testGrammar name grammar examples =
  describe name $
    for_ examples $ \(expectedSyntax, expectedString) -> do
      it ("should parse from " <> expectedString <> " correctly") $ do
        let actualSyntax = [parsed | (parsed, "") <- parseG grammar expectedString]
        listToMaybe actualSyntax `shouldBe` Just expectedSyntax
      it ("should unparse to " <> expectedString <> " correctly") $ do
        let actualString = unparseG grammar expectedSyntax ""
        actualString `shouldBe` Just expectedString
      it ("should print to " <> expectedString <> " correctly") $ do
        let actualString = ($ "") <$> printG grammar expectedSyntax
        actualString `shouldBe` Just expectedString
