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

  describe "arithGrammar" $
    for_ arithExamples $ \(expectedArith, str) -> do
      it ("should parse " <> str <> " correctly") $ do
        let actualArith = [parsedArith | (parsedArith, "") <- parseG arithGrammar str]
        actualArith `shouldBe` [expectedArith]
      it ("should unparse " <> show expectedArith <> " correctly") $ do
        let unparsedArith = unparseG arithGrammar expectedArith ""
        unparsedArith `shouldBe` Just str
      it ("should print " <> show expectedArith <> " correctly") $ do
        let printedArith = ($ "") <$> printG arithGrammar expectedArith
        printedArith `shouldBe` Just str

  describe "jsonGrammar" $
    for_ jsonExamples $ \(expectedJson, str) -> do
      it ("should parse " <> str <> " correctly") $ do
        let actualJson = [parsedJson | (parsedJson, "") <- parseG jsonGrammar str]
        actualJson `shouldBe` [expectedJson]
      it ("should unparse " <> show expectedJson <> " correctly") $ do
        let unparsedJson = unparseG jsonGrammar expectedJson ""
        unparsedJson `shouldBe` Just str
      it ("should print " <> show expectedJson <> " correctly") $ do
        let printedJson = ($ "") <$> printG jsonGrammar expectedJson
        printedJson `shouldBe` Just str

  describe "sexprGrammar" $
    for_ sexprExamples $ \(expectedSExpr, str) -> do
      it ("should parse " <> str <> " correctly") $ do
        let actualSExpr = [parsedSExpr | (parsedSExpr, "") <- parseG sexprGrammar str]
        actualSExpr `shouldBe` [expectedSExpr]
      it ("should unparse " <> show expectedSExpr <> " correctly") $ do
        let unparsedSExpr = unparseG sexprGrammar expectedSExpr ""
        unparsedSExpr `shouldBe` Just str
      it ("should print " <> show expectedSExpr <> " correctly") $ do
        let printedSExpr = ($ "") <$> printG sexprGrammar expectedSExpr
        printedSExpr `shouldBe` Just str

  describe "lambdaGrammar" $
    for_ lambdaExamples $ \(expectedLambda, str) -> do
      it ("should parse " <> str <> " correctly") $ do
        let actualLambda = [parsedLambda | (parsedLambda, "") <- parseG lambdaGrammar str]
        actualLambda `shouldBe` [expectedLambda]
      it ("should unparse " <> show expectedLambda <> " correctly") $ do
        let unparsedLambda = unparseG lambdaGrammar expectedLambda ""
        unparsedLambda `shouldBe` Just str
      it ("should print " <> show expectedLambda <> " correctly") $ do
        let printedLambda = ($ "") <$> printG lambdaGrammar expectedLambda
        printedLambda `shouldBe` Just str
