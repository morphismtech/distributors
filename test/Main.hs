module Main (main) where

import Data.Foldable hiding (toList)
import Data.Maybe (listToMaybe)
import Control.Lens.Grammar
import Control.Lens.Grammar.BackusNaur
import Test.DocTest
import Test.Hspec

import Examples.RegString
import Examples.Arithmetic
import Examples.Json
import Examples.SExpr
import Examples.Lambda
import Examples.LenVec
import Examples.SemVer

main :: IO ()
main = do
  doctests
  hspec $ do
    describe "regexGrammar" $ for_ regexExamples $ testGrammarExample regexGrammar
    describe "semverGrammar" $ for_ semverExamples $ testCtxGrammarExample semverGrammar
    describe "semverCtxGrammar" $ for_ semverExamples $ testCtxGrammarExample semverCtxGrammar
    describe "arithGrammar" $ for_ arithExamples $ testGrammarExample arithGrammar
    describe "jsonGrammar" $ for_ jsonExamples $ testCtxGrammarExample jsonGrammar
    describe "sexprGrammar" $ for_ sexprExamples $ testCtxGrammarExample sexprGrammar
    describe "lambdaGrammar" $ for_ lambdaExamples $ testCtxGrammarExample lambdaGrammar
    describe "lenvecGrammar" $ for_ lenvecExamples $ testCtxGrammarExample lenvecGrammar

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
  it ("should match from " <> expectedString <> " correctly") $ do
    let actualMatch = expectedString =~ regbnfG grammar
    actualMatch `shouldBe` True

testCtxGrammarExample :: (Show a, Eq a) => CtxGrammar Char a -> (a, String) -> Spec
testCtxGrammarExample grammar (expectedSyntax, expectedString) = do
  it ("should parse from " <> expectedString <> " correctly") $ do
    let actualSyntax = [parsed | (parsed, "") <- parseG grammar expectedString]
    listToMaybe actualSyntax `shouldBe` Just expectedSyntax
  it ("should unparse to " <> expectedString <> " correctly") $ do
    let actualString = unparseG grammar expectedSyntax ""
    actualString `shouldBe` Just expectedString
  it ("should print to " <> expectedString <> " correctly") $ do
    let actualString = ($ "") <$> printG grammar expectedSyntax
    actualString `shouldBe` Just expectedString
