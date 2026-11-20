module Main (main) where

import Test.Hspec

import Properties.Json
import Properties.TypeScript

main :: IO ()
main = hspec $ do
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
  jsonElementsSpec
  typeScriptSpec

