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
numberProperties = do
  naturalGrammarProperties
  integerGrammarProperties

naturalGrammarProperties :: Spec
naturalGrammarProperties = describe "naturalGrammar" $ do
  prop "parsecG and unparsecG round-trip decimal exactly like Read/Show" $
    \(NonNegative n) ->
      let str = show (n :: Integer)
          nat = fromInteger n :: Natural
      in parsecResult (parsecG naturalGrammar str) == Just nat
         && parsecStream (parsecG naturalGrammar str) == ""
         && parsecResult (unparsecG naturalGrammar nat "") == Just nat
         && parsecStream (unparsecG naturalGrammar nat "") == str
  prop "parsecG accepts 0x/0X-prefixed hexadecimal like Read; unparsecG normalizes to decimal" $
    \(NonNegative n) ->
      let nat = fromInteger n :: Natural
          str = "0x" ++ showHex nat ""
      in parsecResult (parsecG naturalGrammar str) == Just nat
         && parsecStream (parsecG naturalGrammar str) == ""
         && parsecStream (unparsecG naturalGrammar nat "") == show nat
  prop "parsecG accepts 0o/0O-prefixed octal like Read; unparsecG normalizes to decimal" $
    \(NonNegative n) ->
      let nat = fromInteger n :: Natural
          str = "0o" ++ showOct nat ""
      in parsecResult (parsecG naturalGrammar str) == Just nat
         && parsecStream (parsecG naturalGrammar str) == ""
         && parsecStream (unparsecG naturalGrammar nat "") == show nat
  it "matches GHC's Read on concrete decimal, octal and hexadecimal examples" $ do
    let cases =
          [ ("0", 0), ("017", 17), ("255", 255)
          , ("0o17", 15), ("0O17", 15)
          , ("0x1f", 31), ("0X1F", 31), ("0x1F", 31)
          , ("0xff", 255), ("0XFF", 255)
          ]
    for_ cases $ \(str, expected) -> do
      parsecResult (parsecG naturalGrammar str :: ParsecState String Natural)
        `shouldBe` Just expected
      parsecStream (parsecG naturalGrammar str :: ParsecState String Natural)
        `shouldBe` ""
  it "commits after a prefix with no digits, unlike Read's unlimited backtracking" $ do
    -- Read leaves "o"/"x" unconsumed and succeeds with 0; a genuinely
    -- LL(1) grammar, limited to one token of lookahead, cannot backtrack
    -- that far, so it fails outright instead. Accepted trade-off for LL(1).
    parsecResult (parsecG naturalGrammar "0o" :: ParsecState String Natural)
      `shouldBe` Nothing
    parsecResult (parsecG naturalGrammar "0x" :: ParsecState String Natural)
      `shouldBe` Nothing
  it "unparsecG renders hexadecimal- and octal-derived values as canonical decimal" $ do
    parsecStream (unparsecG naturalGrammar (255 :: Natural) "") `shouldBe` "255"
    parsecStream (unparsecG naturalGrammar (15 :: Natural) "") `shouldBe` "15"
    parsecStream (unparsecG naturalGrammar (0 :: Natural) "") `shouldBe` "0"

integerGrammarProperties :: Spec
integerGrammarProperties = describe "integerGrammar" $ do
  prop "parsecG and unparsecG round-trip signed decimal exactly like Read/Show" $
    \(n :: Integer) ->
      let str = show n
      in parsecResult (parsecG integerGrammar str) == Just n
         && parsecStream (parsecG integerGrammar str) == ""
         && parsecResult (unparsecG integerGrammar n "") == Just n
         && parsecStream (unparsecG integerGrammar n "") == str
  prop "parsecG accepts a signed 0x/0X hexadecimal magnitude; unparsecG normalizes to decimal" $
    \(n :: Integer) ->
      let str = (if n < 0 then "-" else "") ++ "0x" ++ showHex (abs n) ""
      in parsecResult (parsecG integerGrammar str) == Just n
         && parsecStream (parsecG integerGrammar str) == ""
         && parsecStream (unparsecG integerGrammar n "") == show n
  prop "parsecG accepts a signed 0o/0O octal magnitude; unparsecG normalizes to decimal" $
    \(n :: Integer) ->
      let str = (if n < 0 then "-" else "") ++ "0o" ++ showOct (abs n) ""
      in parsecResult (parsecG integerGrammar str) == Just n
         && parsecStream (parsecG integerGrammar str) == ""
         && parsecStream (unparsecG integerGrammar n "") == show n
  it "matches GHC's Read on concrete signed decimal, octal and hexadecimal examples" $ do
    let cases =
          [ ("0", 0), ("-0", 0), ("017", 17), ("-017", -17)
          , ("255", 255), ("-255", -255)
          , ("0o17", 15), ("-0o17", -15)
          , ("0x1f", 31), ("-0x1f", -31), ("0X1F", 31)
          ]
    for_ cases $ \(str, expected) -> do
      parsecResult (parsecG integerGrammar str :: ParsecState String Integer)
        `shouldBe` Just expected
      parsecStream (parsecG integerGrammar str :: ParsecState String Integer)
        `shouldBe` ""
  it "rejects a leading + and a sign detached from its digits by whitespace, like Read" $ do
    -- "+5" isn't a recognized sign at all, matching Read. "- 5" is
    -- accepted by Read (it re-skips whitespace before every lexeme,
    -- including after the sign) but rejected here, for the same
    -- deliberate no-whitespace-skipping reason naturalGrammar gives.
    parsecResult (parsecG integerGrammar "+5" :: ParsecState String Integer)
      `shouldBe` Nothing
    parsecResult (parsecG integerGrammar "- 5" :: ParsecState String Integer)
      `shouldBe` Nothing
  it "unparsecG never prints a redundant sign on zero" $ do
    parsecStream (unparsecG integerGrammar (0 :: Integer) "") `shouldBe` "0"
  it "unparsecG renders hexadecimal- and octal-derived values as canonical signed decimal" $ do
    parsecStream (unparsecG integerGrammar (255 :: Integer) "") `shouldBe` "255"
    parsecStream (unparsecG integerGrammar (-255 :: Integer) "") `shouldBe` "-255"
    parsecStream (unparsecG integerGrammar (-15 :: Integer) "") `shouldBe` "-15"
