module Examples.Floating
  ( doubleExamples
  , floatExamples
  , doubleSyntaxExamples
  ) where

-- | Round trip examples for `doubleGrammar`. `doubleGrammar` always
-- prints & unparses exactly as `show` would, so every expected string
-- here is literally what `show` produces for the paired `Double`.
doubleExamples :: [(Double, String)]
doubleExamples =
  [ (0.0, "0.0")
  , (-0.0, "-0.0")
  , (1.5, "1.5")
  , (-1.5, "-1.5")
  , (42.0, "42.0")
  , (100000.0, "100000.0")
  , (10000000.0, "1.0e7")
  , (0.1, "0.1")
  , (0.01, "1.0e-2")
  , (1.0e20, "1.0e20")
  , (1.0e-5, "1.0e-5")
  , (1 / 0, "Infinity")
  , (-1 / 0, "-Infinity")
  ]

-- | Round trip examples for `floatGrammar`, `doubleGrammar`'s `Float`
-- analogue.
floatExamples :: [(Float, String)]
floatExamples =
  [ (0.0, "0.0")
  , (1.5, "1.5")
  , (-1.5, "-1.5")
  , (100000.0, "100000.0")
  , (1 / 0, "Infinity")
  ]

-- | Alternative syntaxes that `doubleGrammar` should still parse,
-- even though it never prints them; see `FloatingSyntax`. Each string
-- parses to the paired `Double`. `NaN` is excluded here since `NaN /=
-- NaN` would make it useless in an equality-based table; it's tested
-- separately.
doubleSyntaxExamples :: [(String, Double)]
doubleSyntaxExamples =
  [ ("1", 1.0)
  , ("1e10", 1.0e10)
  , ("1.5e+10", 1.5e10)
  , ("1.5E10", 1.5e10)
  ]
