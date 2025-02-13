module Main (main) where

import Data.Char
import Data.Foldable
import Text.Grammar.Distributor
import Test.Hspec

expectedRegexGrammar :: [(String, RegEx)]
expectedRegexGrammar =
  [("start",NonTerminal "regex")
  ,("alternate",Sequence (NonTerminal "sequence") (KleeneStar (Sequence (Terminal "|") (NonTerminal "sequence"))))
  ,("any",Terminal ".")
  ,("atom",Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (NonTerminal "nonterminal") (NonTerminal "fail")) (NonTerminal "in-class")) (NonTerminal "not-in-class")) (NonTerminal "in-category")) (NonTerminal "char")) (NonTerminal "any")) (NonTerminal "parenthesized"))
  ,("char",Alternate (NonTerminal "literal") (NonTerminal "escaped"))
  ,("escaped",Sequence (Terminal "\\") (InClass "$()*+.?[\\]^{|}"))
  ,("expression",Alternate (Alternate (Alternate (Alternate (NonTerminal "terminal") (NonTerminal "kleene-optional")) (NonTerminal "kleene-star")) (NonTerminal "kleene-plus")) (NonTerminal "atom"))
  ,("fail",Terminal "\\q")
  ,("in-category",Sequence (Sequence (Terminal "\\p{") (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Alternate (Terminal "Lu") (Terminal "Ll")) (Terminal "Lt")) (Terminal "Lm")) (Terminal "Lo")) (Terminal "Mn")) (Terminal "Mc")) (Terminal "Me")) (Terminal "Nd")) (Terminal "Nl")) (Terminal "No")) (Terminal "Pc")) (Terminal "Pd")) (Terminal "Ps")) (Terminal "Pe")) (Terminal "Pi")) (Terminal "Pf")) (Terminal "Po")) (Terminal "Sm")) (Terminal "Sc")) (Terminal "Sk")) (Terminal "So")) (Terminal "Zs")) (Terminal "Zl")) (Terminal "Zp")) (Terminal "Cc")) (Terminal "Cf")) (Terminal "Cs")) (Terminal "Co")) (Terminal "Cn"))) (Terminal "}"))
  ,("in-class",Sequence (Sequence (Terminal "[") (KleeneStar (NonTerminal "char"))) (Terminal "]"))
  ,("kleene-optional",Sequence (NonTerminal "atom") (Terminal "?"))
  ,("kleene-plus",Sequence (NonTerminal "atom") (Terminal "+"))
  ,("kleene-star",Sequence (NonTerminal "atom") (Terminal "*"))
  ,("literal",NotInClass "$()*+.?[\\]^{|}")
  ,("nonterminal",Sequence (Sequence (Terminal "\\q{") (KleeneStar (NonTerminal "char"))) (Terminal "}"))
  ,("not-in-class",Sequence (Sequence (Terminal "[^") (KleeneStar (NonTerminal "char"))) (Terminal "]"))
  ,("parenthesized",Sequence (Sequence (Terminal "(") (NonTerminal "regex")) (Terminal ")"))
  ,("regex",Alternate (NonTerminal "alternate") (NonTerminal "fail"))
  ,("sequence",KleenePlus (NonTerminal "expression"))
  ,("terminal",KleenePlus (NonTerminal "char"))
  ]

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
  , (InClass "abc", "[abc]")
  , (NotInClass "abc", "[^abc]")
  , (InCategory UppercaseLetter, "\\p{Lu}")
  , (NonTerminal "rule-name", "\\q{rule-name}")
  ]

main :: IO ()
main = hspec $ do
  describe "RegEx Grammar Test" $ do
    it "should generate a correct grammar" $
      genGrammar regexGrammar `shouldBe` expectedRegexGrammar
  describe "RegEx Print Test" $ do
    for_ regexExamples $ \(rex, str) -> do
      it ("should print " <> show rex <> " correctly") $
        ($ "") <$> genShowS regexGrammar rex `shouldBe` Just str
  describe "RegEx Parse Test" $ do
    for_ regexExamples $ \(rex, str) -> do
      it ("should parse " <> str <> " correctly") $
        genReadS regexGrammar str `shouldSatisfy` ((rex,"") `elem`)
