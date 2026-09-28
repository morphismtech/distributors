module Properties.Number (numberProperties) where

import Control.Lens.Grammar
import Control.Lens.Grammar.Number
import Data.Foldable (for_)
import Numeric (showHex, showOct)
import Numeric.Natural
import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck

numberProperties :: Spec
numberProperties = describe "natGrammar" $ do
  prop "parsecG and unparsecG round-trip decimal exactly like Read/Show" $
    \(NonNegative n) ->
      let str = show (n :: Integer)
          nat = fromInteger n :: Natural
      in parsecResult (parsecG natGrammar str) == Just nat
         && parsecStream (parsecG natGrammar str) == ""
         && parsecResult (unparsecG natGrammar nat "") == Just nat
         && parsecStream (unparsecG natGrammar nat "") == str
  prop "parsecG accepts 0x/0X-prefixed hexadecimal like Read; unparsecG normalizes to decimal" $
    \(NonNegative n) ->
      let nat = fromInteger n :: Natural
          str = "0x" ++ showHex nat ""
      in parsecResult (parsecG natGrammar str) == Just nat
         && parsecStream (parsecG natGrammar str) == ""
         && parsecStream (unparsecG natGrammar nat "") == show nat
  prop "parsecG accepts 0o/0O-prefixed octal like Read; unparsecG normalizes to decimal" $
    \(NonNegative n) ->
      let nat = fromInteger n :: Natural
          str = "0o" ++ showOct nat ""
      in parsecResult (parsecG natGrammar str) == Just nat
         && parsecStream (parsecG natGrammar str) == ""
         && parsecStream (unparsecG natGrammar nat "") == show nat
  it "matches GHC's Read on concrete decimal, octal and hexadecimal examples" $ do
    let cases =
          [ ("0", 0), ("017", 17), ("255", 255)
          , ("0o17", 15), ("0O17", 15)
          , ("0x1f", 31), ("0X1F", 31), ("0x1F", 31)
          , ("0xff", 255), ("0XFF", 255)
          ]
    for_ cases $ \(str, expected) -> do
      parsecResult (parsecG natGrammar str :: ParsecState String Natural)
        `shouldBe` Just expected
      parsecStream (parsecG natGrammar str :: ParsecState String Natural)
        `shouldBe` ""
  it "commits after a prefix with no digits, unlike Read's unlimited backtracking" $ do
    -- Read leaves "o"/"x" unconsumed and succeeds with 0; a genuinely
    -- LL(1) grammar, limited to one token of lookahead, cannot backtrack
    -- that far, so it fails outright instead. Accepted trade-off for LL(1).
    parsecResult (parsecG natGrammar "0o" :: ParsecState String Natural)
      `shouldBe` Nothing
    parsecResult (parsecG natGrammar "0x" :: ParsecState String Natural)
      `shouldBe` Nothing
  it "unparsecG renders hexadecimal- and octal-derived values as canonical decimal" $ do
    parsecStream (unparsecG natGrammar (255 :: Natural) "") `shouldBe` "255"
    parsecStream (unparsecG natGrammar (15 :: Natural) "") `shouldBe` "15"
    parsecStream (unparsecG natGrammar (0 :: Natural) "") `shouldBe` "0"
