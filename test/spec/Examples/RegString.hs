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

  -- Boolean OR (>||<) operations
  , (tokenClass (oneOf "abc" >||< oneOf "xyz"), "[abcxyz]")
  , (tokenClass (notOneOf "abc" >||< notOneOf "xyz"), "[^]")
  , (tokenClass (oneOf "abc" >||< notOneOf "xyz"), "[abc]|[^xyz]")
  , (tokenClass (notOneOf "abc" >||< oneOf "xyz"), "[^abc]|[xyz]")
  , (tokenClass (asIn UppercaseLetter >||< asIn LowercaseLetter), "\\p{Lu}|\\p{Ll}")
  , (tokenClass (notAsIn Control >||< notAsIn Space), "[^]")
  , (tokenClass (oneOf "abc" >||< asIn DecimalNumber), "[abc]|\\p{Nd}")
  , (tokenClass (notOneOf "xyz" >||< notAsIn UppercaseLetter), "[^]")

  -- Boolean AND (>&&<) operations
  , (tokenClass (oneOf "abcdef" >&&< oneOf "def123"), "[def]")
  , (tokenClass (notOneOf "abc" >&&< notOneOf "xyz"), "[^abcxyz]")
  , (tokenClass (oneOf "abcd" >&&< notOneOf "cd"), "[ab]")
  , (tokenClass (notOneOf "abc" >&&< asIn LowercaseLetter), "[^abc\\p{Ll}]")
  , (tokenClass (notOneOf "abc" >&&< notAsIn Control), "[^abc\\P{Cc}]")
  , (tokenClass (asIn UppercaseLetter >&&< notOneOf "XYZ"), "[^XYZ\\p{Lu}]")
  , (tokenClass (notAsIn Control >&&< notAsIn Space), "\\P{Zs|Cc}")
  , (tokenClass (oneOf "0123456789" >&&< asIn DecimalNumber), "[0123456789]")

  -- Boolean NOT (notB) operations
  , (tokenClass (notB (oneOf "abc")), "[^abc]")
  , (tokenClass (notB (notOneOf "abc")), "[abc]")
  , (tokenClass (notB (oneOf "abc" >||< oneOf "xyz")), "[^abcxyz]")
  , (tokenClass (notB (asIn UppercaseLetter)), "\\P{Lu}")
  , (tokenClass (notB (notAsIn Control)), "\\p{Cc}")
  , (tokenClass (notB (notOneOf "abc" >&&< asIn LowercaseLetter)), "[abc]|\\P{Ll}")

  -- fromBool operations
  , (tokenClass (fromBool True), "[^]")
  , (tokenClass (fromBool False), "[]")

  -- Complex combinations
  , (tokenClass (notOneOf "abc" >&&< (asIn LowercaseLetter >||< asIn UppercaseLetter)), "[^abc\\p{Ll}]|\\p{Lu}")
  , (tokenClass ((oneOf "123" >||< asIn DecimalNumber) >&&< notOneOf "789"), "[123]|[^789\\p{Nd}]")
  , (tokenClass (notB (oneOf "abc" >||< asIn MathSymbol)), "[^abc\\P{Sm}]")
  ]
