module Main (main) where

import Data.Char
import Data.Foldable hiding (toList)
import Control.Lens.Grammar
import Control.Lens.Grammar.Boole
import Control.Lens.Grammar.Kleene
import Control.Lens.Grammar.Symbol
import GHC.Exts
import Test.Hspec

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
  describe "regexGrammar" $
    for_ regexExamples $ \(rex, str) -> do
      it ("should print " <> show (runRegString rex) <> " correctly") $
        toList rex `shouldBe` str
      it ("should parse " <> str <> " correctly") $ do
        fromString str `shouldBe` rex
