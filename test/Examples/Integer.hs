module Examples.Integer
  ( integerExamples
  , integerSyntaxExamples
  ) where

-- | Round trip examples for `integerGrammar`. `integerGrammar` always
-- prints & unparses to decimal, so every expected string here is a
-- plain (optionally @-@-signed) decimal numeral.
integerExamples :: [(Integer, String)]
integerExamples =
  [ (0, "0")
  , (7, "7")
  , (-7, "-7")
  , (42, "42")
  , (-42, "-42")
  , (1000000, "1000000")
  ]

-- | Alternative syntaxes that `integerGrammar` should still parse,
-- alongside signed decimal, even though it never prints them; see
-- `IntegerSyntax`. Each string parses to the paired `Integer`.
integerSyntaxExamples :: [(String, Integer)]
integerSyntaxExamples =
  [ ("-007", -7)
  , ("-0o52", -42)
  , ("-0O52", -42)
  , ("-0x2a", -42)
  , ("-0X2A", -42)
  , ("0x2A", 42)
  ]
