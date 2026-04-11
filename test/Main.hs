module Main (main) where

import Data.Foldable hiding (toList)
import Control.Lens.Grammar
import Control.Monad (when)
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
import Properties.Kleene

main :: IO ()
main = do
  hspec $ do
    describe "regexGrammar" $ for_ regexExamples $ testGrammar False regexGrammar
    describe "semverGrammar" $ for_ semverExamples $ testCtxGrammar True semverGrammar
    describe "semverCtxGrammar" $ for_ semverExamples $ testCtxGrammar True semverCtxGrammar
    describe "arithGrammar" $ for_ arithExamples $ testGrammar True arithGrammar
    describe "jsonGrammar" $ for_ jsonExamples $ testCtxGrammar False jsonGrammar
    describe "sexprGrammar" $ for_ sexprExamples $ testCtxGrammar True sexprGrammar
    describe "lambdaGrammar" $ for_ lambdaExamples $ testCtxGrammar True lambdaGrammar
    describe "lenvecGrammar" $ for_ lenvecExamples $ testCtxGrammar True lenvecGrammar
    describe "chainGrammar" $ for_ chainExamples $ testCtxGrammar True chainGrammar
    describe "Kleene" kleeneProperties
    describe "doctest" $
      it "runs module documentation examples" doctests

doctests :: IO ()
doctests = do
  let
    modulePaths =
      [ "src/Control/Lens/Grammar.hs" ]
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

testGrammar :: (Show a, Eq a) => Bool -> Grammar Char a -> (a, String) -> Spec
testGrammar isLL1 grammar (expectedSyntax, expectedString) = do
  testCtxGrammar isLL1 grammar (expectedSyntax, expectedString)
  it ("should match " <> expectedString <> " correctly") $ do
    let actualMatch = expectedString =~ regbnfG grammar
    actualMatch `shouldBe` True

testCtxGrammar :: (Show a, Eq a) => Bool -> CtxGrammar Char a -> (a, String) -> Spec
testCtxGrammar isLL1 grammar (expectedSyntax, expectedString) = do
  it ("should parseG from " <> expectedString <> " correctly") $ do
    let actualSyntax = [parsed | (parsed, "") <- parseG grammar expectedString]
    actualSyntax `shouldBe` [expectedSyntax]
  it ("should unparseG to " <> expectedString <> " correctly") $ do
    let actualString = unparseG grammar expectedSyntax ""
    actualString `shouldBe` Just expectedString
  it ("should printG to " <> expectedString <> " correctly") $ do
    let actualString = ($ "") <$> printG grammar expectedSyntax
    actualString `shouldBe` Just expectedString
  when isLL1 $ do
    it ("should parsecG from " <> expectedString <> " correctly") $ do
      let actualSyntax = parsecG grammar expectedString
      let expectedLength = genericLength expectedString
      let actualLooked = parsecLooked actualSyntax
      let actualError  = parsecError  actualSyntax
      actualSyntax `shouldBe`
        (ParsecState actualLooked expectedLength "" actualError (Just expectedSyntax))
    it ("should unparsecG to " <> expectedString <> " correctly") $ do
      let actualString = unparsecG grammar expectedSyntax ""
      let expectedLength = genericLength expectedString
      let actualLooked = parsecLooked actualString
      let actualError  = parsecError  actualString
      actualString `shouldBe`
        (ParsecState actualLooked expectedLength expectedString actualError (Just expectedSyntax))
