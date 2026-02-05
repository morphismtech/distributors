module Examples.LenVec
  ( LenVec
  , lenvecGrammar
  , lenvecExamples
  ) where

import Control.Lens.Grammar
import Control.Lens.Grammar.Symbol
import Control.Lens.Grammar.Token
import Control.Lens.PartialIso
import Data.Profunctor.Distributor
import Data.Profunctor.Monoidal
import qualified Data.Profunctor.Monadic as P
import Numeric.Natural

data LenVec = LenVec {length :: Natural, vector :: [Natural]}
  deriving (Eq, Ord, Show, Read)

makeNestedPrisms ''LenVec

lenvecGrammar :: CtxGrammar Char LenVec
lenvecGrammar = _LenVec >? P.do
  let numberG = iso show read >~ someP (asIn @Char DecimalNumber)
  len <- numberG *< terminal ";"
  if len == 0 then return [] else
    let
      lenSub1 = fromIntegral len - 1
      headG = numberG
      tailG = replicateP lenSub1 $ P.do
        terminal ","
        numberG
    in
      headG >:< tailG

lenvecExamples :: [(LenVec, String)]
lenvecExamples =
  [ (LenVec 3 [1,2,3], "3;1,2,3")
  , (LenVec 0 [], "0;")
  ]
