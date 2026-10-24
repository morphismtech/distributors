module Examples.RegString
  ( regexExamples
  ) where

import Control.Lens.Grammar

regexExamples :: [(RegString, String)]
regexExamples =
  [ (terminal "abc123etc.", "abc123etc.")
  , (terminal "x" <> terminal "y", "xy")
  , (falseP, "[]")
  , (terminal "xy" >|< terminal "z", "xy|z")
  , (token 'x' >|< token 'y', "[xy]")
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

  -- Boolean OR (>|<) operations
  , (tokenClass (oneOf "abc" >|< oneOf "xyz"), "[abcxyz]")
  , (tokenClass (oneOf "abc" >|< notOneOf "xyz"), "[abc]|[^xyz]")
  , (tokenClass (notOneOf "abc" >|< oneOf "xyz"), "[^abc]|[xyz]")
  , (tokenClass (asIn UppercaseLetter >|< asIn LowercaseLetter), "\\p{Lu}|\\p{Ll}")
  , (tokenClass (oneOf "abc" >|< asIn DecimalNumber), "[abc]|\\p{Nd}")

  -- Boolean AND (>&&<) operations
  , (tokenClass (oneOf "abcdef" >&&< oneOf "def123"), "[def]")
  , (tokenClass (notOneOf "abc" >&&< notOneOf "xyz"), "[^abcxyz]")
  , (tokenClass (oneOf "abcd" >&&< notOneOf "cd"), "[ab]")
  , (tokenClass (notOneOf "abc" >&&< asIn LowercaseLetter), "[^abc\\p{Ll}]")
  , (tokenClass (notOneOf "abc" >&&< notAsIn Control), "[^abc\\P{Cc}]")
  , (tokenClass (asIn UppercaseLetter >&&< notOneOf "XYZ"), "[^XYZ\\p{Lu}]")
  , (tokenClass (notAsIn Control >&&< notAsIn Space), "\\P{Zs|Cc}")
  , (tokenClass (oneOf "0123456789xyz" >&&< asIn DecimalNumber), "[0123456789]")

  -- Boolean NOT (notP) operations
  , (tokenClass (notP (oneOf "abc")), "[^abc]")
  , (tokenClass (notP (notOneOf "abc")), "[abc]")
  , (tokenClass (notP (oneOf "abc" >|< oneOf "xyz")), "[^abcxyz]")
  , (tokenClass (notP (asIn UppercaseLetter)), "\\P{Lu}")
  , (tokenClass (notP (notAsIn Control)), "\\p{Cc}")
  , (tokenClass (notP (notOneOf "abc" >&&< asIn LowercaseLetter)), "[abc]|\\P{Ll}")

  -- trueP & falseP
  , (tokenClass trueP, "[^]")
  , (tokenClass falseP, "[]")

  -- Complex combinations
  , (tokenClass (notOneOf "abc" >&&< (asIn LowercaseLetter >|< asIn UppercaseLetter)), "[^abc\\p{Ll}]|\\p{Lu}")
  , (tokenClass ((oneOf "123" >|< asIn DecimalNumber) >&&< notOneOf "789"), "[123]|[^789\\p{Nd}]")
  , (tokenClass (notP (oneOf "abc" >|< asIn MathSymbol)), "[^abc\\P{Sm}]")
  ]
