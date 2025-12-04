module Main (main) where

import Data.Char
import Data.Foldable hiding (toList)
import Data.String
import GHC.Exts
import Control.Lens.Grammar
import Control.Lens.Grammar.Kleene
import Control.Lens.Grammar.Symbol
import Control.Lens.Grammar.Token
import Test.Hspec

-- expectedRegexGrammar :: [(String, RegExStr)]
-- expectedRegexGrammar = []
  -- [("start",nonTerminal "regex")
  -- ,("alternate",Sequence (nonTerminal "sequence") (KleeneStar (Sequence (terminal "|") (nonTerminal "sequence"))))
  -- ,("any",terminal ".")
  -- ,("atom",Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (nonTerminal "nonterminal") (nonTerminal "fail")) (nonTerminal "class-in")) (nonTerminal "class-not-in")) (nonTerminal "category-in")) (nonTerminal "category-not-in")) (nonTerminal "char")) (nonTerminal "any")) (nonTerminal "parenthesized"))
  -- ,("category",Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (terminal "Ll") (terminal "Lu")) (terminal "Lt")) (terminal "Lm")) (terminal "Lo")) (terminal "Mn")) (terminal "Mc")) (terminal "Me")) (terminal "Nd")) (terminal "Nl")) (terminal "No")) (terminal "Pc")) (terminal "Pd")) (terminal "Ps")) (terminal "Pe")) (terminal "Pi")) (terminal "Pf")) (terminal "Po")) (terminal "Sm")) (terminal "Sc")) (terminal "Sk")) (terminal "So")) (terminal "Zs")) (terminal "Zl")) (terminal "Zp")) (terminal "Cc")) (terminal "Cf")) (terminal "Cs")) (terminal "Co")) (terminal "Cn"))
  -- ,("category-in",Sequence (Sequence (terminal "\\p{") (nonTerminal "category")) (terminal "}"))
  -- ,("category-not-in",Sequence (Sequence (terminal "\\P{") (nonTerminal "category")) (terminal "}"))
  -- ,("char",Alternate (nonTerminal "char-literal") (nonTerminal "char-escaped"))
  -- ,("char-escaped",Sequence (terminal "\\") (oneOf "$()*+.?[\\]^{|}"))
  -- ,("char-literal",notOneOf "$()*+.?[\\]^{|}")
  -- ,("class-in",Sequence (Sequence (terminal "[") (KleeneStar (nonTerminal "char"))) (terminal "]"))
  -- ,("class-not-in",Sequence (Sequence (terminal "[^") (KleeneStar (nonTerminal "char"))) (terminal "]"))
  -- ,("expression",Alternate (Alternate (Alternate (Alternate (nonTerminal "terminal") (nonTerminal "kleene-optional")) (nonTerminal "kleene-star")) (nonTerminal "kleene-plus")) (nonTerminal "atom"))
  -- ,("fail",terminal "\\q")
  -- ,("kleene-optional",Sequence (nonTerminal "atom") (terminal "?"))
  -- ,("kleene-plus",Sequence (nonTerminal "atom") (terminal "+"))
  -- ,("kleene-star",Sequence (nonTerminal "atom") (terminal "*"))
  -- ,("nonterminal",Sequence (Sequence (terminal "\\q{") (KleeneStar (nonTerminal "char"))) (terminal "}"))
  -- ,("parenthesized",Sequence (Sequence (terminal "(") (nonTerminal "regex")) (terminal ")"))
  -- ,("regex",nonTerminal "alternate")
  -- ,("sequence",KleeneStar (nonTerminal "expression"))
  -- ,("terminal",plusK (nonTerminal "char"))
  -- ]

regexExamples :: [(RegString, String)]
regexExamples =
  [ (terminal "abc123etc.", "abc123etc\\.")
  , (terminal "x" <> terminal "y", "xy")
  , (zeroK, "\\q")
  , (terminal "x" >|< terminal "y", "x|y")
  , (optK (terminal "x"), "x?")
  , (starK (terminal "x"), "x*")
  , (plusK (terminal "x"), "x+")
  , (anyToken, ".")
  , (oneOf "abc", "[abc]")
  , (notOneOf "abc", "[^abc]")
  , (asIn UppercaseLetter, "\\p{Lu}")
  , (notAsIn LowercaseLetter, "\\P{Ll}")
  , (nonTerminal "rule-name", "\\q{rule-name}")
  , (terminal "", "")
  ]

main :: IO ()
main = hspec $ do
  describe "regexGrammar" $ do
    -- it "should generate a correct grammar" $
    --   genGrammar regexGrammar `shouldBe` expectedRegexGrammar
    for_ regexExamples $ \(rex, str) -> do
      it ("should print " <> show (runRegString rex) <> " correctly") $
        toList rex `shouldBe` str
      it ("should parse " <> str <> " correctly") $ do
        fromString str `shouldBe` rex
