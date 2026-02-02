module Main (main) where

import Data.Foldable (for_)
import Test.DocTest

main :: IO ()
main = for_
  [ "src/Control/Lens/Grammar.hs"
  , "src/Control/Lens/Grammar/Token.hs"
  ] $ \modulePath -> do
    putStr "Testing module documentation in "
    putStrLn modulePath
    doctest
      [ modulePath
      , "-XLambdaCase"
      , "-XDerivingStrategies"
      , "-XImpredicativeTypes"
      , "-XQuantifiedConstraints"
      , "-XTypeFamilies"
      , "-XFunctionalDependencies"
      , "-XDefaultSignatures"
      ]
