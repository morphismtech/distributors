module Examples.Chain
  ( Chain (..)
  , chainGrammar
  , chainExamples
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.Grammar
import Control.Lens.Grammar.BackusNaur
import Control.Lens.Grammar.Symbol
import Control.Lens.Grammar.Token
import Control.Lens.PartialIso
import Data.Profunctor.Monoidal
import Data.Profunctor.Separator

data Chain
  = Emp
  | Char Char
  | Seq Chain Chain
  deriving stock (Eq, Ord, Show, Read)

makePrisms ''Chain

chainGrammar :: CtxGrammar Char Chain
chainGrammar = ruleRec "chain" seqG
  where
    seqG chn = rule "seq" $
      chain Left _Seq _Emp noSep (atomG chn)
    atomG chn = rule "atom" $
      _Char >? charG <|> terminal "(" >* chn *< terminal ")"
    charG = notOneOf "()\\"
      <|> terminal "\\" >* oneOf "()\\"

chainExamples :: [(Chain, String)]
chainExamples =
  [ (Char 'x', "x")
  , (Seq (Char '1') (Char '2'), "12")
  , (Seq (Seq (Char 'x') (Char 'y')) (Char 'z'), "xyz")
  , (Seq (Char 'x') (Seq (Char 'y') (Char 'z')), "x(yz)")
  , (Emp, "")
  ]
