module Main (main) where

import Test.DocTest

main :: IO ()
main = doctest
  [ "-isrc"
  , "src/Text/Grammar/Distributor.hs"
  , "-XLambdaCase"
  , "-XDefaultSignatures"
  , "-XDerivingVia"
  , "-XImpredicativeTypes"
  , "-XUndecidableInstances"
  , "-XQuantifiedConstraints"
  , "-XFunctionalDependencies"
  , "-XDerivingVia"
  ]
