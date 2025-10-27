module Control.Lens.Grammar.BackusNaur
  ( BackusNaurForm (..)
  , Gram (..)
  , liftGram0
  , liftGram1
  , liftGram2
  ) where

import Control.Lens.Grammar.Kleene
import Control.Lens.Grammar.Token
import Control.Lens.Grammar.Symbol
import Data.Function
import Data.Set as Set

class BackusNaurForm gram where
  rule :: String -> gram -> gram
  rule _ = id
  ruleRec :: String -> (gram -> gram) -> gram
  ruleRec _ = fix

data Gram rule = Gram
  { startGram :: rule
  , rulesGram :: Set (String, rule)
  } deriving stock (Eq, Ord)

instance (Ord rule, NonTerminalSymbol rule)
  => BackusNaurForm (Gram rule) where
    rule name = ruleRec name . const
    ruleRec name f =
      let
        start = nonTerminal name
        Gram newRule oldRules = f (Gram start mempty)
        rules = insert (name, newRule) oldRules
      in
        Gram start rules

instance (Ord t, TerminalSymbol t)
  => TerminalSymbol (Gram t) where
  type Alphabet (Gram t) = Alphabet t
  terminal = liftGram0 . terminal

liftGram0 :: Ord a => a -> Gram a
liftGram0 a = Gram a mempty

liftGram1 :: (a -> a) -> Gram a -> Gram a
liftGram1 f (Gram start rules) = Gram (f start) rules

liftGram2 :: Ord a => (a -> a -> a) -> Gram a -> Gram a -> Gram a
liftGram2 f (Gram start0 rules0) (Gram start1 rules1) =
  Gram (f start0 start1) (rules0 <> rules1)

instance (Ord p, Tokenized p) => Tokenized (Gram p) where
  type Token (Gram p) = Token p
  anyToken = liftGram0 anyToken
  noToken = liftGram0 noToken
  token = liftGram0 . token
  notToken = liftGram0 . notToken
  oneOf = liftGram0 . oneOf
  notOneOf = liftGram0 . notOneOf
  asIn = liftGram0 . asIn
  notAsIn = liftGram0 . notAsIn

instance (Ord t, KleeneStarAlgebra t) => KleeneStarAlgebra (Gram t) where
  starK = liftGram1 starK
  plusK = liftGram1 plusK
  optK = liftGram1 optK
  empK = liftGram0 empK
  (>|<) = liftGram2 (>|<)
instance (Ord t, Monoid t) => Monoid (Gram t) where
  mempty = liftGram0 mempty
instance (Ord t, Semigroup t) => Semigroup (Gram t) where
  (<>) = liftGram2 (<>)
