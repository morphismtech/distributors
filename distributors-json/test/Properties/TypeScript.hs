module Properties.TypeScript (typeScriptSpec) where

import Control.Lens.Grammar (ParsecState (..), parsecG, unparsecG)
import Control.Lens.Grammar.TypeScript
import Data.Foldable (toList)
import Data.Sequence qualified as Seq
import Test.Hspec

typeScriptSpec :: Spec
typeScriptSpec = describe "tsGrammar" $ do
  it "parses a declaration file as its canonical print parses" $ do
    fixture <- readFile "test/Properties/fixture.d.ts"
    golden <- readFile "test/Properties/fixture.golden.d.ts"
    let parsed = declarations fixture
    parsed `shouldSatisfy` (/= Nothing)
    parsed `shouldBe` declarations golden
  it "prints a declaration file canonically" $ do
    golden <- readFile "test/Properties/fixture.golden.d.ts"
    fmap source (declarations golden) `shouldBe` Just golden
  it "locates failures" $
    parsecOffset (parsecG tsGrammar (tokens "interface A { a: number; b: }"))
      `shouldBe` 9

-- | Tokens, scanned without their trivia.
tokens :: String -> [TsToken]
tokens = concat . parsecResult . parsecG tsTokensGrammar

-- | Declarations, parsed from all of their tokens.
declarations :: String -> Maybe [TsDeclaration]
declarations text = case parsecG tsGrammar (tokens text) of
  parsed | null (parsecStream parsed) -> parsecResult parsed
  _ -> Nothing

-- | Print declarations, as tokens & characters, into sequences.
source :: [TsDeclaration] -> String
source decls = toList $ parsecStream $ unparsecG tsTokensGrammar
  (toList (parsecStream (unparsecG tsGrammar decls (Seq.empty @TsToken))))
  (Seq.empty @Char)
