module Main (main) where

import Data.Foldable hiding (toList)
import Data.Maybe (listToMaybe)
import Control.Lens.Grammar
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
    testGrammar "regexGrammar" regexGrammar regexExamples
    testGrammar "semverGrammar" semverGrammar semverExamples
    testGrammar "semverCtxGrammar" semverCtxGrammar semverExamples
    testGrammar "arithGrammar" arithGrammar arithExamples
    testGrammar "jsonGrammar" jsonGrammar jsonExamples
    testGrammar "sexprGrammar" sexprGrammar sexprExamples
    testGrammar "lambdaGrammar" lambdaGrammar lambdaExamples
    testGrammar "lenvecGrammar" lenvecGrammar lenvecExamples

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
