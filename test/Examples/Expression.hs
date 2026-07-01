module Examples.Expression
  ( Expr (..)
  , exprGrammar
  , exprExamples
  , powGrammar
  , powExamples
  , leftGrammar
  , leftExamples
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.Grammar
import Numeric.Natural

data Expr
  = Nat Natural
  | Exp Expr Expr
  | Mul Expr Expr
  | Div Expr Expr
  | Add Expr Expr
  | Sub Expr Expr
  deriving stock (Eq, Ord, Show, Read)

makePrisms ''Expr

-- | An expression grammar over natural numbers, built with `withOperators`
-- from a precedence table: parenthesization binds tightest, then a
-- right-associative exponent @^@, then left-associative @*@ & @/@, then
-- left-associative @+@ & @-@.
exprGrammar :: Grammar Char Expr
exprGrammar = ruleRec "expr" $ \expr ->
  let
    atom = rule "atom" $
      nat <|> terminal "(" >* expr *< terminal ")"
    nat = rule "nat" $
      _Nat . iso show read >? someP (asIn @Char DecimalNumber)
  in withOperators
    [ [ InfixR _Exp (terminal "^") ]
    , [ InfixL _Mul (terminal "*"), InfixL _Div (terminal "/") ]
    , [ InfixL _Add (terminal "+"), InfixL _Sub (terminal "-") ]
    ] atom

exprExamples :: [(Expr, String)]
exprExamples =
  [ (Nat 42, "42")
  , (Add (Nat 1) (Nat 2), "1+2")
  , (Sub (Sub (Nat 3) (Nat 2)) (Nat 1), "3-2-1")
  , (Div (Div (Nat 8) (Nat 2)) (Nat 2), "8/2/2")
  , (Exp (Nat 2) (Exp (Nat 3) (Nat 2)), "2^3^2")
  , (Add (Mul (Nat 2) (Nat 3)) (Nat 4), "2*3+4")
  , (Sub (Nat 1) (Div (Nat 6) (Nat 3)), "1-6/3")
  , (Mul (Exp (Nat 2) (Nat 3)) (Nat 4), "2^3*4")
  , (Mul (Nat 2) (Add (Nat 3) (Nat 4)), "2*(3+4)")
  , (Exp (Add (Nat 1) (Nat 2)) (Nat 3), "(1+2)^3")
  ]

-- | A purely right-associative grammar built directly with `chain1` @Right@,
-- so it exercises `chainr1` / `difoldr` independently of `withOperators`.
-- This is a regression test for the right-fold: @2^3^2@ must associate as
-- @Exp 2 (Exp 3 2)@, not @Exp 3 (Exp 2 2)@.
powGrammar :: Grammar Char Expr
powGrammar = ruleRec "pow" $ \e ->
  let
    atom = rule "atom" $
      nat <|> terminal "(" >* e *< terminal ")"
    nat = rule "nat" $
      _Nat . iso show read >? someP (asIn @Char DecimalNumber)
  in chain1 (\x -> Right x) _Exp (sepWith "^") atom

powExamples :: [(Expr, String)]
powExamples =
  [ (Nat 2, "2")
  , (Exp (Nat 2) (Nat 3), "2^3")
  , (Exp (Nat 2) (Exp (Nat 3) (Nat 2)), "2^3^2")
  , (Exp (Nat 2) (Exp (Nat 3) (Exp (Nat 4) (Nat 5))), "2^3^4^5")
  ]

-- | A purely left-associative expression grammar (no right-associative
-- exponent) built with `withOperators`. Because every level is a single
-- associativity, `withOperators` parses each leading term exactly once, so
-- unlike the mixed `exprGrammar` this one is LL1 and is tested against the
-- predictive @parsecG@ / megaparsec backends (@testCfg True@).
leftGrammar :: Grammar Char Expr
leftGrammar = ruleRec "expr" $ \expr ->
  let
    atom = rule "atom" $
      nat <|> terminal "(" >* expr *< terminal ")"
    nat = rule "nat" $
      _Nat . iso show read >? someP (asIn @Char DecimalNumber)
  in withOperators
    [ [ InfixL _Mul (terminal "*"), InfixL _Div (terminal "/") ]
    , [ InfixL _Add (terminal "+"), InfixL _Sub (terminal "-") ]
    ] atom

leftExamples :: [(Expr, String)]
leftExamples =
  [ (Nat 7, "7")
  , (Sub (Sub (Nat 3) (Nat 2)) (Nat 1), "3-2-1")
  , (Div (Div (Nat 8) (Nat 2)) (Nat 2), "8/2/2")
  , (Sub (Add (Nat 1) (Mul (Nat 2) (Nat 3))) (Nat 4), "1+2*3-4")
  , (Mul (Add (Nat 1) (Nat 2)) (Nat 3), "(1+2)*3")
  ]
