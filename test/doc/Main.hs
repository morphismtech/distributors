module Main (main) where

import Data.Foldable (for_)
import Test.DocTest

main :: IO ()
main = do
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
