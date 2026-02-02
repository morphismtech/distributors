module Main (main) where

import Test.DocTest

main :: IO ()
main = doctest
  [ "src/Control/Lens/Grammar.hs" 
  , "-XLambdaCase"
  , "-XDerivingStrategies"
  , "-XImpredicativeTypes"
  , "-XQuantifiedConstraints"
  , "-XTypeFamilies"
  ]
