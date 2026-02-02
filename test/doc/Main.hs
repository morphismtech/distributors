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
      [ "-XLambdaCase"
      , "-XDerivingStrategies"
      , "-XImpredicativeTypes"
      , "-XQuantifiedConstraints"
      , "-XTypeFamilies"
      , "-XFunctionalDependencies"
      , "-XDefaultSignatures"
      ]
  for_ modulePaths $ \modulePath -> do
    putStr "Testing module documentation in "
    putStrLn modulePath
    doctest (modulePath : languageExtensions)
