module Examples.RegString
  ( regexExamples
  ) where

import Control.Lens.Grammar
import Control.Lens.Grammar.Boole
import Control.Lens.Grammar.Kleene
import Control.Lens.Grammar.Symbol
import Control.Lens.Grammar.Token

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
