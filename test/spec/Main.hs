module Main (main) where

import Data.Char
import Data.Foldable hiding (toList)
import Control.Lens.Grammar
import Control.Lens.Grammar.BackusNaur
import Control.Lens.Grammar.Boole
import Control.Lens.Grammar.Kleene
import Control.Lens.Grammar.Symbol
import Data.Profunctor
import Data.Profunctor.Grammar
import GHC.Exts
import Test.Hspec

expectedRegexGrammar :: Bnf RegString
expectedRegexGrammar = Bnf
  { startBnf = fromString "\\q{regex}"
  , rulesBnf = fromList $ map (second' fromString)
    [ ("alternate","\\q{sequence}(\\|\\q{sequence})*")
    , ("atom","(\\\\q\\{)\\q{char}*\\}|\\q{char}|\\q{char-class}|\\(\\q{regex}\\)")
    , ("category","Ll|Lu|Lt|Lm|Lo|Mn|Mc|Me|Nd|Nl|No|Pc|Pd|Ps|Pe|Pi|Pf|Po|Sm|Sc|Sk|So|Zs|Zl|Zp|Cc|Cf|Cs|Co|Cn")
    , ("category-test","(\\\\p\\{)\\q{category}\\}|(\\\\P\\{)(\\q{category}(\\|\\q{category})*)\\}")
    , ("char","[^\\(\\)\\*\\+\\?\\[\\\\\\]\\^\\{\\|\\}\\P{Cc}]|\\\\\\q{char-escaped}")
    , ("char-any","\\[\\^\\]|\\\\P\\{\\}|\\[\\^\\\\P\\{\\}\\]")
    , ("char-class","\\q{fail}|\\q{char-any}|\\q{one-of}|(\\[\\^)\\q{char}+(\\q{category-test}?\\])|\\q{category-test}")
    , ("char-control","NUL|SOH|STX|ETX|EOT|ENQ|ACK|BEL|BS|HT|LF|VT|FF|CR|SO|SI|DLE|DC1|DC2|DC3|DC4|NAK|SYN|ETB|CAN|EM|SUB|ESC|FS|GS|RS|US|DEL|PAD|HOP|BPH|NBH|IND|NEL|SSA|ESA|HTS|HTJ|VTS|PLD|PLU|RI|SS2|SS3|DCS|PU1|PU2|STS|CCH|MW|SPA|EPA|SOS|SGCI|SCI|CSI|ST|OSC|PM|APC")
    , ("char-escaped","[\\(\\)\\*\\+\\?\\[\\\\\\]\\^\\{\\|\\}]|\\q{char-control}")
    , ("expression","\\q{atom}\\?|\\q{atom}\\*|\\q{atom}\\+|\\q{atom}")
    , ("fail","\\[\\]")
    , ("one-of","\\[\\q{char}+\\]")
    , ("regex","\\q{alternate}")
    , ("sequence","\\q{char}*|\\q{expression}*")
    ]
  }

regexExamples :: [(RegString, String)]
regexExamples =
  [ (terminal "abc123etc.", "abc123etc.")
  , (terminal "x" <> terminal "y", "xy")
  , (zeroK, "[]")
  , (terminal "x" >|< terminal "y", "x|y")
  , (optK (terminal "x"), "x?")
  , (starK (terminal "x"), "x*")
  , (plusK (terminal "x"), "x+")
  , (anyToken, "[^]")
  , (oneOf "abc", "[abc]")
  , (notOneOf "abc", "[^abc]")
  , (asIn UppercaseLetter, "\\p{Lu}")
  , (notAsIn LowercaseLetter, "\\P{Ll}")
  , (nonTerminal "rule-name", "\\q{rule-name}")
  , (terminal "", "")
  , (optK (terminal "abc"), "(abc)?")
  , (optK (terminal "abc") <> nonTerminal "xyz", "(abc)?\\q{xyz}")
  , (tokenClass (oneOf "abc" >||< oneOf "xyz"), "[abcxyz]")
  , (tokenClass (notOneOf "abc" >&&< asIn LowercaseLetter), "[^abc\\p{Ll}]")
  , (tokenClass (notOneOf "abc" >&&< notAsIn Control), "[^abc\\P{Cc}]")
  ]

main :: IO ()
main = hspec $ do
  describe "regexGrammar" $ do
    it "should generate a correct grammar" $ do
      runGrammor regexGrammar `shouldBe` expectedRegexGrammar
    for_ regexExamples $ \(rex, str) -> do
      it ("should print " <> show (runRegString rex) <> " correctly") $
        toList rex `shouldBe` str
      it ("should parse " <> str <> " correctly") $ do
        fromString str `shouldBe` rex
