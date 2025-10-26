module Control.Lens.Grammar.BackusNaur
  ( BackusNaurForm (..)
  , Gram (..)
  ) where

import Control.Lens.Grammar.Kleene
import Control.Lens.Grammar.Token
import Control.Lens.Grammar.Symbol
import Data.Function
import Data.Set as Set

class BackusNaurForm a where
  rule :: String -> a -> a
  rule _ = id
  ruleRec :: String -> (a -> a) -> a
  ruleRec _ = fix

data Gram a = Gram
  { startGram :: a
  , rulesGram :: Set (String, a)
  } deriving stock (Eq, Ord)

instance (Ord a, NonTerminalSymbol a)
  => BackusNaurForm (Gram a) where
    rule name = ruleRec name . const
    ruleRec name f =
      let
        start = nonTerminal name
        Gram newRule oldRules = f (Gram start mempty)
        rules = insert (name, newRule) oldRules
      in
        Gram start rules

instance (Ord a, TerminalSymbol a) => TerminalSymbol (Gram a) where
  type Alphabet (Gram a) = Alphabet a
  terminal = liftGram0 . terminal

liftGram0 :: Ord a => a -> Gram a
liftGram0 a = Gram a mempty

liftGram1 :: (a -> a) -> Gram a -> Gram a
liftGram1 f (Gram start rules) = Gram (f start) rules

liftGram2 :: Ord a => (a -> a -> a) -> Gram a -> Gram a -> Gram a
liftGram2 f (Gram start0 rules0) (Gram start1 rules1) =
  Gram (f start0 start1) (rules0 <> rules1)

instance (Ord a, Tokenized a) => Tokenized (Gram a) where
  type Token (Gram a) = Token a
  anyToken = liftGram0 anyToken
  noToken = liftGram0 noToken
  token = liftGram0 . token
  notToken = liftGram0 . notToken
  oneOf = liftGram0 . oneOf
  notOneOf = liftGram0 . notOneOf
  asIn = liftGram0 . asIn
  notAsIn = liftGram0 . notAsIn

instance (Ord a, KleeneStarAlgebra a) => KleeneStarAlgebra (Gram a) where
  starK = liftGram1 starK
  plusK = liftGram1 plusK
  optK = liftGram1 optK
  empK = liftGram0 empK
  (>|<) = liftGram2 (>|<)
instance (Ord a, Monoid a) => Monoid (Gram a) where
  mempty = liftGram0 mempty
instance (Ord a, Semigroup a) => Semigroup (Gram a) where
  (<>) = liftGram2 (<>)
