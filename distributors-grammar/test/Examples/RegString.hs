module Examples.RegString
  ( regexExamples
  ) where

import Control.Lens.Grammar

regexExamples :: [(RegEx Char, String)]
regexExamples =
  [ (terminal "abc123etc.", "abc123etc.")
  , (terminal "x" <> terminal "y", "xy")
  , (falseP, "[]")
  , (terminal "xy" >|< terminal "z", "xy|z")
  , (token 'x' >|< token 'y', "[xy]")
  , (optK (terminal "x"), "x?")
  , (starK (terminal "x"), "x*")
  , (plusK (terminal "x"), "x+")
  , (tokenAny, "[^]")
  , (oneOf "abc", "[a-c]")
  , (notOneOf "abc", "[^a-c]")
  , (asIn UppercaseLetter, "\\p{Lu}")
  , (notAsIn LowercaseLetter, "\\P{Ll}")
  , (nonTerminal "rule-name", "\\q{rule-name}")
  , (terminal "", "")
  , (optK (terminal "abc"), "(abc)?")
  , (optK (terminal "abc") <> nonTerminal "xyz", "(abc)?\\q{xyz}")

  -- Boolean OR (>|<) operations
  , (tokenClass (oneOf "abc" >|< oneOf "xyz"), "[a-cx-z]")
  , (tokenClass (oneOf "abc" >|< notOneOf "xyz"), "[^x-z]")
  , (tokenClass (notOneOf "abc" >|< oneOf "xyz"), "[^a-c]")
  , (tokenClass (asIn UppercaseLetter >|< asIn LowercaseLetter), "\\p{Lu}|\\p{Ll}")
  , (tokenClass (oneOf "abc" >|< asIn DecimalNumber), "[a-c]|\\p{Nd}")

  -- Boolean AND (>&<) operations
  , (tokenClass (oneOf "abcdef" >&< oneOf "def123"), "[d-f]")
  , (tokenClass (notOneOf "abc" >&< notOneOf "xyz"), "[^a-cx-z]")
  , (tokenClass (oneOf "abcd" >&< notOneOf "cd"), "[ab]")
  , (tokenClass (notOneOf "abc" >&< asIn LowercaseLetter), "[^a-c\\p{Ll}]")
  , (tokenClass (notOneOf "abc" >&< notAsIn Control), "[^a-c\\P{Cc}]")
  , (tokenClass (asIn UppercaseLetter >&< notOneOf "XYZ"), "[^X-Z\\p{Lu}]")
  , (tokenClass (notAsIn Control >&< notAsIn Space), "\\P{Zs|Cc}")
  , (tokenClass (oneOf "0123456789xyz" >&< asIn DecimalNumber), "[0-9]")

  -- Boolean NOT (notP) operations
  , (tokenClass (notP (oneOf "abc")), "[^a-c]")
  , (tokenClass (notP (notOneOf "abc")), "[a-c]")
  , (tokenClass (notP (oneOf "abc" >|< oneOf "xyz")), "[^a-cx-z]")
  , (tokenClass (notP (asIn UppercaseLetter)), "\\P{Lu}")
  , (tokenClass (notP (notAsIn Control)), "\\p{Cc}")
  , (tokenClass (notP (notOneOf "abc" >&< asIn LowercaseLetter)), "[a-c]|\\P{Ll}")

  -- trueP & falseP
  , (tokenClass trueP, "[^]")
  , (tokenClass falseP, "[]")

  -- Complex combinations
  , (tokenClass (notOneOf "abc" >&< (asIn LowercaseLetter >|< asIn UppercaseLetter)), "[^a-c\\p{Ll}]|\\p{Lu}")
  , (tokenClass ((oneOf "123" >|< asIn DecimalNumber) >&< notOneOf "789"), "[^7-9\\p{Nd}]")
  , (tokenClass (notP (oneOf "abc" >|< asIn MathSymbol)), "[^a-c\\P{Sm}]")
  ]
