module Examples.Arithmetic
  ( Arith (..)
  , arithGrammar
  , arithExamples
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.Grammar
import Numeric.Natural

data Arith
  = Num Natural
  | Add Arith Arith
  | Mul Arith Arith
  deriving stock (Eq, Ord, Show, Read)

makePrisms ''Arith

arithGrammar :: Grammar Char Arith
arithGrammar = ruleRec "arith" sumG
  where
    sumG arith = rule "sum" $
      chain1 Left _Add (sepWith "+") (prodG arith)
    prodG arith = rule "product" $
      chain1 Left _Mul (sepWith "*") (factorG arith)
    factorG arith = rule "factor" $
      number <|> terminal "(" >* arith *< terminal ")"
    number = rule "number" $
      _Num . iso show read >? someP (asIn @Char DecimalNumber)

arithExamples :: [(Arith, String)]
arithExamples =
  [ (Num 42, "42")
  , (Add (Num 1) (Num 2), "1+2")
  , (Add (Mul (Num 2) (Num 3)) (Num 4), "2*3+4")
  , (Mul (Num 2) (Add (Num 3) (Num 4)), "2*(3+4)")
  , (Add (Add (Num 1) (Mul (Num 2) (Num 3))) (Num 4), "1+2*3+4")
  ]
