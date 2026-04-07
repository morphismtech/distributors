module Main (main) where

import Data.Foldable hiding (toList)
import Control.Lens.Grammar
import Data.List (genericLength)
import Test.DocTest
import Test.Hspec

import Examples.Arithmetic
import Examples.Chain
import Examples.Json
import Examples.Lambda
import Examples.LenVec
import Examples.RegString
import Examples.SemVer
import Examples.SExpr

main :: IO ()
main = do
  hspec $ do
    describe "regexGrammar" $ for_ regexExamples $ testGrammarExample regexGrammar
    describe "semverGrammar" $ for_ semverExamples $ testCtxGrammarExample semverGrammar
    describe "semverCtxGrammar" $ for_ semverExamples $ testCtxGrammarExample semverCtxGrammar
    describe "arithGrammar" $ for_ arithExamples $ testGrammarExample arithGrammar
    describe "jsonGrammar" $ for_ jsonExamples $ testCtxGrammarExample jsonGrammar
    describe "sexprGrammar" $ for_ sexprExamples $ testCtxGrammarExample sexprGrammar
    describe "lambdaGrammar" $ for_ lambdaExamples $ testCtxGrammarExample lambdaGrammar
    describe "lenvecGrammar" $ for_ lenvecExamples $ testCtxGrammarExample lenvecGrammar
    describe "chainGrammar" $ for_ chainExamples $ testCtxGrammarExample chainGrammar
  doctests

doctests :: IO ()
doctests = do
  let
    modulePaths =
      [ "src/Control/Lens/Grammar.hs"
      , "src/Control/Lens/Grammar/Token.hs"
      ]
    languageExtensions =
      [ "-XAllowAmbiguousTypes"
      , "-XArrows"
      , "-XConstraintKinds"
      , "-XDataKinds"
      , "-XDefaultSignatures"
      , "-XDeriveFoldable"
      , "-XDeriveFunctor"
      , "-XDeriveTraversable"
      , "-XDeriveGeneric"
      , "-XDerivingStrategies"
      , "-XDerivingVia"
      , "-XEmptyCase"
      , "-XFlexibleContexts"
      , "-XFlexibleInstances"
      , "-XFunctionalDependencies"
      , "-XGADTs"
      , "-XGeneralizedNewtypeDeriving"
      , "-XImportQualifiedPost"
      , "-XImpredicativeTypes"
      , "-XInstanceSigs"
      , "-XLambdaCase"
      , "-XMagicHash"
      , "-XMonoLocalBinds"
      , "-XQuantifiedConstraints"
      , "-XRankNTypes"
      , "-XRecursiveDo"
      , "-XScopedTypeVariables"
      , "-XStandaloneDeriving"
      , "-XStandaloneKindSignatures"
      , "-XTemplateHaskell"
      , "-XTupleSections"
      , "-XTypeApplications"
      , "-XTypeFamilies"
      , "-XTypeOperators"
      , "-XUndecidableInstances"
      , "-XUndecidableSuperClasses"
      ]
  for_ modulePaths $ \modulePath -> do
    putStr "Testing module documentation in "
    putStrLn modulePath
    doctest (modulePath : languageExtensions)

testGrammarExample :: (Show a, Eq a) => Grammar Char a -> (a, String) -> Spec
testGrammarExample grammar (expectedSyntax, expectedString) = do
  testCtxGrammarExample grammar (expectedSyntax, expectedString)
  it ("should match " <> expectedString <> " correctly") $ do
    let actualMatch = expectedString =~ regbnfG grammar
    actualMatch `shouldBe` True

testCtxGrammarExample :: (Show a, Eq a) => CtxGrammar Char a -> (a, String) -> Spec
testCtxGrammarExample grammar (expectedSyntax, expectedString) = do
  it ("should parseG from " <> expectedString <> " correctly") $ do
    let actualSyntax = [parsed | (parsed, "") <- parseG grammar expectedString]
    actualSyntax `shouldBe` [expectedSyntax]
  it ("should unparseG to " <> expectedString <> " correctly") $ do
    let actualString = unparseG grammar expectedSyntax ""
    actualString `shouldBe` Just expectedString
  it ("should printG to " <> expectedString <> " correctly") $ do
    let actualString = ($ "") <$> printG grammar expectedSyntax
    actualString `shouldBe` Just expectedString
  it ("should parsecG from " <> expectedString <> " correctly") $ do
    let actualSyntax = parsecG grammar expectedString
    let expectedLength = genericLength expectedString
    let actualExpect = parsecExpect actualSyntax
    actualSyntax `shouldBe`
      (Reply expectedLength actualExpect (Just expectedSyntax) "")
  it ("should unparsecG to " <> expectedString <> " correctly") $ do
    let actualString = unparsecG grammar expectedSyntax ""
    let expectedLength = genericLength expectedString
    actualString `shouldBe`
      (Reply expectedLength falseB (Just expectedSyntax) expectedString)
