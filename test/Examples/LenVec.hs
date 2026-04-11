module Examples.LenVec
  ( LenVec
  , lenvecGrammar
  , lenvecExamples
  ) where

import Control.Lens.Grammar
import qualified Data.Profunctor.Monadic as P
import Numeric.Natural

data LenVec = LenVec {length :: Natural, vector :: [Natural]}
  deriving (Eq, Ord, Show, Read)

makeNestedPrisms ''LenVec

lenvecGrammar :: CtxGrammar Char LenVec
lenvecGrammar = _LenVec >? P.do
  let
    numberG = iso show read >~ someP (asIn @Char DecimalNumber)
    vectorG n = intercalateP n (sepWith ",") numberG
  len <- numberG             -- bonds to _LenVec
  terminal ";"               -- doesn't bond
  vectorG (fromIntegral len) -- bonds to _LenVec

lenvecExamples :: [(LenVec, String)]
lenvecExamples =
  [ (LenVec 3 [1,2,3], "3;1,2,3")
  , (LenVec 0 [], "0;")
  ]
