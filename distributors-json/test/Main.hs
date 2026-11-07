module Main (main) where

import Control.Monad (when)
import Data.Foldable (for_)
import Data.Maybe (isJust)
import System.Environment (lookupEnv)
import Test.DocTest
import Test.Hspec

import Properties.Json
import Properties.TypeScript

main :: IO ()
main = do
  shouldRunDoctests <- isJust <$> lookupEnv "DISTRIBUTORS_RUN_DOCTESTS"
  hspec $ do
    when shouldRunDoctests $
      describe "doctest" $
        it "should run haddock examples" doctests
    jsonTypeSpec
    aesonSpec
    jsonErrorSpec
    jsonObjectSpec
    jsonOptionsSpec
    jsonTupleSpec
    jsonTupleChoiceSpec
    jsonOptionalSpec
    jsonCodecSpec
    jsonPrintSpec
    typeScriptSpec

doctests :: IO ()
doctests = do
  stackExe <- lookupEnv "STACK_EXE"
  ghcEnvironment <- lookupEnv "GHC_ENVIRONMENT"
  let
    modulePaths =
      [ "src/Control/Lens/Grammar/Json.hs"
      , "src/Control/Lens/Grammar/TypeScript.hs"
      ]
    packageEnvFlags = case ghcEnvironment of
      Just "-" -> []
      Just path -> ["-package-env=" <> path]
      Nothing -> []
    runnerFlags
      | isJust stackExe = []
      | otherwise = "-isrc" : packageEnvFlags
    languageExtensions =
      [ "-XHaskell2010"
      , "-XAllowAmbiguousTypes"
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
    doctest (modulePath : runnerFlags <> languageExtensions)
