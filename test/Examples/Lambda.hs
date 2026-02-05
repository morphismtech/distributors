module Examples.Lambda
  ( Lambda (..)
  , lambdaGrammar
  , lambdaExamples
  ) where

import Control.Lens
import Control.Lens.Grammar
import Control.Lens.Grammar.BackusNaur
import Control.Lens.Grammar.Symbol
import Control.Lens.Grammar.Token
import Control.Lens.PartialIso
import Data.Profunctor.Distributor
import Data.Profunctor.Monoidal

-- | Abstract syntax tree for lambda calculus terms
data Lambda
  = Var String           -- ^ Variable
  | Lam String Lambda    -- ^ Lambda abstraction (\\x.body)
  | App Lambda Lambda    -- ^ Function application
  deriving stock (Eq, Ord, Show, Read)

-- Generate prisms
makePrisms ''Lambda

-- | Grammar for untyped lambda calculus
lambdaGrammar :: Grammar Char Lambda
lambdaGrammar = ruleRec "lambda" termG
  where
    -- Top level term: lambda abstraction or application
    termG term = rule "term" $ choice
      [ lamG term
      , appG term
      ]

    -- Lambda abstraction: \x.body
    lamG term = rule "lambda" $
      _Lam >? terminal "\\" >* varNameG *< terminal "." >*< term

    -- Application: left-associative chain of atoms
    -- e.g., "f x y" parses as "(f x) y"
    appG term = rule "application" $
      chain1 Left _App (sepBy (terminal " ")) (atomG term)

    -- Atomic term: variable or parenthesized term
    atomG term = rule "atom" $ choice
      [ _Var >? varNameG
      , terminal "(" >* term *< terminal ")"
      ]

    -- Variable name: starts with lowercase letter,
    -- followed by alphanumeric or underscore
    varNameG = rule "varname" $ asIn LowercaseLetter >:<
      manyP (choice (token '_' : map asIn [LowercaseLetter, UppercaseLetter, DecimalNumber]))

-- | Example lambda calculus terms for testing
lambdaExamples :: [(Lambda, String)]
lambdaExamples =
  -- Variables
  [ (Var "x", "x")
  , (Var "y", "y")
  , (Var "foo", "foo")
  , (Var "x1", "x1")

  -- Simple lambda abstractions
  , (Lam "x" (Var "x"), "\\x.x")                        -- Identity
  , (Lam "x" (Lam "y" (Var "x")), "\\x.\\y.x")          -- K combinator
  , (Lam "x" (Lam "y" (Var "y")), "\\x.\\y.y")          -- K* combinator

  -- Applications
  , (App (Var "f") (Var "x"), "f x")
  , (App (App (Var "f") (Var "x")) (Var "y"), "f x y")

  -- Lambda with application in body
  , (Lam "f" (Lam "x" (App (Var "f") (Var "x"))),
     "\\f.\\x.f x")

  -- S combinator: \x.\y.\z.x z (y z)
  , (Lam "x" (Lam "y" (Lam "z"
      (App (App (Var "x") (Var "z"))
           (App (Var "y") (Var "z"))))),
     "\\x.\\y.\\z.x z (y z)")

  -- Omega combinator: (\x.x x)(\x.x x)
  , (App (Lam "x" (App (Var "x") (Var "x")))
         (Lam "x" (App (Var "x") (Var "x"))),
     "(\\x.x x) (\\x.x x)")

  -- Church numeral 0: \f.\x.x
  , (Lam "f" (Lam "x" (Var "x")),
     "\\f.\\x.x")

  -- Church numeral 1: \f.\x.f x
  , (Lam "f" (Lam "x" (App (Var "f") (Var "x"))),
     "\\f.\\x.f x")

  -- Church numeral 2: \f.\x.f (f x)
  , (Lam "f" (Lam "x"
      (App (Var "f") (App (Var "f") (Var "x")))),
     "\\f.\\x.f (f x)")

  -- Y combinator: \f.(\x.f (x x)) (\x.f (x x))
  , (Lam "f"
      (App (Lam "x" (App (Var "f") (App (Var "x") (Var "x"))))
           (Lam "x" (App (Var "f") (App (Var "x") (Var "x"))))),
     "\\f.(\\x.f (x x)) (\\x.f (x x))")
  ]
