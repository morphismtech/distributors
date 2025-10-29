module Control.Lens.Grammar.BackusNaur
  ( BackusNaurForm (..)
  , BNF (..)
  , liftBNF0
  , liftBNF1
  , liftBNF2
  ) where

import Control.Lens.Grammar.Kleene
import Control.Lens.Grammar.Token
import Control.Lens.Grammar.Symbol
import Data.Coerce
import Data.Function
import Data.Set as Set

class BackusNaurForm bnf where
  rule :: String -> bnf -> bnf
  rule _ = id
  ruleRec :: String -> (bnf -> bnf) -> bnf
  ruleRec _ = fix

data BNF rule = BNF
  { startBNF :: rule
  , rulesBNF :: Set (String, rule)
  } deriving stock (Eq, Ord, Show, Read)

liftBNF0 :: Ord a => a -> BNF a
liftBNF0 a = BNF a mempty

liftBNF1 :: (Coercible a b, Ord b) => (a -> b) -> BNF a -> BNF b
liftBNF1 f (BNF start rules) = BNF (f start) (Set.map coerce rules)

liftBNF2
  :: (Coercible a c, Coercible b c, Ord c)
  => (a -> b -> c) -> BNF a -> BNF b -> BNF c
liftBNF2 f (BNF start0 rules0) (BNF start1 rules1) =
  BNF (f start0 start1) (Set.map coerce rules0 <> Set.map coerce rules1)

instance (Ord rule, NonTerminalSymbol rule)
  => BackusNaurForm (BNF rule) where
    rule name = ruleRec name . const
    ruleRec name f =
      let
        start = nonTerminal name
        BNF newRule oldRules = f (BNF start mempty)
        rules = insert (name, newRule) oldRules
      in
        BNF start rules

instance (Ord t, TerminalSymbol t)
  => TerminalSymbol (BNF t) where
  type Alphabet (BNF t) = Alphabet t
  terminal = liftBNF0 . terminal

instance (Ord t, NonTerminalSymbol t)
  => NonTerminalSymbol (BNF t) where
  nonTerminal = liftBNF0 . nonTerminal

instance (Ord p, Tokenized p) => Tokenized (BNF p) where
  type Token (BNF p) = Token p
  anyToken = liftBNF0 anyToken
  noToken = liftBNF0 noToken
  token = liftBNF0 . token
  notToken = liftBNF0 . notToken
  oneOf = liftBNF0 . oneOf
  notOneOf = liftBNF0 . notOneOf
  asIn = liftBNF0 . asIn
  notAsIn = liftBNF0 . notAsIn

instance (Ord t, KleeneStarAlgebra t) => KleeneStarAlgebra (BNF t) where
  starK = liftBNF1 starK
  plusK = liftBNF1 plusK
  optK = liftBNF1 optK
  empK = liftBNF0 empK
  (>|<) = liftBNF2 (>|<)
instance (Ord t, Monoid t) => Monoid (BNF t) where
  mempty = liftBNF0 mempty
instance (Ord t, Semigroup t) => Semigroup (BNF t) where
  (<>) = liftBNF2 (<>)
