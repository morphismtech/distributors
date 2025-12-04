module Main (main) where

import Data.Char
import Data.Foldable
import Data.List (nub)
import Control.Lens.Grammar
import Test.Hspec

-- expectedRegexGrammar :: [(String, RegExStr)]
-- expectedRegexGrammar = []
  -- [("start",NonTerminal "regex")
  -- ,("alternate",Sequence (NonTerminal "sequence") (KleeneStar (Sequence (Terminal "|") (NonTerminal "sequence"))))
  -- ,("any",Terminal ".")
  -- ,("atom",Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (NonTerminal "nonterminal") (NonTerminal "fail")) (NonTerminal "class-in")) (NonTerminal "class-not-in")) (NonTerminal "category-in")) (NonTerminal "category-not-in")) (NonTerminal "char")) (NonTerminal "any")) (NonTerminal "parenthesized"))
  -- ,("category",Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Terminal "Ll") (Terminal "Lu")) (Terminal "Lt")) (Terminal "Lm")) (Terminal "Lo")) (Terminal "Mn")) (Terminal "Mc")) (Terminal "Me")) (Terminal "Nd")) (Terminal "Nl")) (Terminal "No")) (Terminal "Pc")) (Terminal "Pd")) (Terminal "Ps")) (Terminal "Pe")) (Terminal "Pi")) (Terminal "Pf")) (Terminal "Po")) (Terminal "Sm")) (Terminal "Sc")) (Terminal "Sk")) (Terminal "So")) (Terminal "Zs")) (Terminal "Zl")) (Terminal "Zp")) (Terminal "Cc")) (Terminal "Cf")) (Terminal "Cs")) (Terminal "Co")) (Terminal "Cn"))
  -- ,("category-in",Sequence (Sequence (Terminal "\\p{") (NonTerminal "category")) (Terminal "}"))
  -- ,("category-not-in",Sequence (Sequence (Terminal "\\P{") (NonTerminal "category")) (Terminal "}"))
  -- ,("char",Alternate (NonTerminal "char-literal") (NonTerminal "char-escaped"))
  -- ,("char-escaped",Sequence (Terminal "\\") (OneOf "$()*+.?[\\]^{|}"))
  -- ,("char-literal",NotOneOf "$()*+.?[\\]^{|}")
  -- ,("class-in",Sequence (Sequence (Terminal "[") (KleeneStar (NonTerminal "char"))) (Terminal "]"))
  -- ,("class-not-in",Sequence (Sequence (Terminal "[^") (KleeneStar (NonTerminal "char"))) (Terminal "]"))
  -- ,("expression",Alternate (Alternate (Alternate (Alternate (NonTerminal "terminal") (NonTerminal "kleene-optional")) (NonTerminal "kleene-star")) (NonTerminal "kleene-plus")) (NonTerminal "atom"))
  -- ,("fail",Terminal "\\q")
  -- ,("kleene-optional",Sequence (NonTerminal "atom") (Terminal "?"))
  -- ,("kleene-plus",Sequence (NonTerminal "atom") (Terminal "+"))
  -- ,("kleene-star",Sequence (NonTerminal "atom") (Terminal "*"))
  -- ,("nonterminal",Sequence (Sequence (Terminal "\\q{") (KleeneStar (NonTerminal "char"))) (Terminal "}"))
  -- ,("parenthesized",Sequence (Sequence (Terminal "(") (NonTerminal "regex")) (Terminal ")"))
  -- ,("regex",NonTerminal "alternate")
  -- ,("sequence",KleeneStar (NonTerminal "expression"))
  -- ,("terminal",KleenePlus (NonTerminal "char"))
  -- ]

regexExamples :: [(RegEx, String)]
regexExamples =
  [ (Terminal "abc123etc.", "abc123etc\\.")
  , (Sequence (Terminal "x") (Terminal "y"), "xy")
  , (Fail, "\\q")
  , (Alternate (Terminal "x") (Terminal "y"), "x|y")
  , (KleeneOpt (Terminal "x"), "x?")
  , (KleeneStar (Terminal "x"), "x*")
  , (KleenePlus (Terminal "x"), "x+")
  , (AnyChar, ".")
  , (OneOf "abc", "[abc]")
  , (NotOneOf "abc", "[^abc]")
  , (AsIn UppercaseLetter, "\\p{Lu}")
  , (NotAsIn LowercaseLetter, "\\P{Ll}")
  , (NonTerminal "rule-name", "\\q{rule-name}")
  , (Terminal "", "")
  ]

main :: IO ()
main = hspec $ do
  describe "regexGrammar" $ do
    it "should generate a correct grammar" $
      genGrammar regexGrammar `shouldBe` expectedRegexGrammar
    for_ regexExamples $ \(rex, str) -> do
      it ("should print " <> show rex <> " correctly") $
        showGrammar regexGrammar rex `shouldBe` Just str
      it ("should parse " <> str <> " correctly") $ do
        let parses = readGrammar regexGrammar str
        parses `shouldSatisfy` elem rex
        length (nub (map regexNorm parses)) `shouldBe` 1
