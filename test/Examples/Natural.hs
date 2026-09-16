module Examples.Natural
  ( naturalExamples
  , naturalSyntaxExamples
  ) where

import Numeric.Natural

-- | Round trip examples for `naturalGrammar`. `naturalGrammar` always
-- prints & unparses to decimal, so every expected string here is a
-- plain decimal numeral.
naturalExamples :: [(Natural, String)]
naturalExamples =
  [ (0, "0")
  , (7, "7")
  , (42, "42")
  , (1000000, "1000000")
  ]

-- | Alternative syntaxes that `naturalGrammar` should still parse,
-- alongside decimal, even though it never prints them; see
-- `NaturalSyntax`. Each string parses to the paired `Natural`.
naturalSyntaxExamples :: [(String, Natural)]
naturalSyntaxExamples =
  [ ("007", 7)
  , ("0o52", 42)
  , ("0O52", 42)
  , ("0x2a", 42)
  , ("0X2A", 42)
  , ("0x2A", 42)
  ]
