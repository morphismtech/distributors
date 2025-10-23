module Control.Lens.Grammar
  ( -- *
    RegGrammar
  , Grammar
  , CtxGrammar
  , Gram (..)
  , genRegEx
  , genGram
  , genShowS
  , genReadS
  , Grammatical (..)
  , Regular
  , Grammaticator
  , Contextual
  , NonTerminalSymbol (..)
  ) where

import Control.Applicative
import Control.Lens.RegEx
import Control.Lens.Token
import Control.Lens.Stream
import Control.Monad
import Data.Function
import Data.Monoid
import Data.Profunctor
import Data.Profunctor.Distributor
import Data.Profunctor.Monadic
import Data.Profunctor.Syntax
import Data.Set (insert, Set)
import GHC.Exts
import Type.Reflection
import Witherable

type RegGrammar c a = forall p. Regular c p => p a a
type Grammar c a = forall p. Grammaticator c p => p a a
type CtxGrammar s a = forall p m. Contextual s m p => p s s m a a

data Gram c = Gram
  { startGram :: (All, RegEx c)
  , rulesGram :: Set (String, (All, RegEx c))
  }

genGram
  :: (Categorized c, Ord c, Ord (Categorize c))
  => Grammar c a
  -> Gram c
genGram gram = case runInvariantP gram of (rules, start) -> Gram start rules

genRegEx :: Categorized c => RegGrammar c a -> RegEx c
genRegEx = runInvariantP

genShowS
  :: (Filterable m, MonadPlus m)
  => CtxGrammar String a -> a -> m ShowS
genShowS = runPrintor . toPrintor

genReadS :: CtxGrammar String a -> ReadS a
genReadS = runParsor

type Regular c p =
  ( Terminator c p
  , Tokenizor c p
  , Alternator p
  )

type Grammaticator c p =
  ( Regular c p
  , Filtrator p
  , forall x. Grammatical (p x x)
  )

type Contextual s m p =
  ( IsStream s, Grammaticator (Item s) (p s s m)
  , Alternative m, Filterable m, MonadPlus m
  , Polyadic p, Tetradic m p
  )

class Grammatical a where
  rule :: String -> a -> a
  rule _ = id
  ruleRec :: String -> (a -> a) -> a
  ruleRec _ = fix
instance Grammatical (Parsor s t m a b)
instance Grammatical (Printor s t m a b)
instance Grammatical (Lintor s t m a b)
instance (NonTerminalSymbol a, Ord a)
  => Grammatical (Set (String, a), a) where
    rule name = ruleRec name . const
    ruleRec name f =
      let
        start = nonTerminal name
        (oldRules, newRule)  = f (mempty, start)
        rules = insert (name, newRule) oldRules
      in
        (rules, start)
instance Grammatical p => Grammatical (InvariantP p a b) where
  rule name = InvariantP . rule name . runInvariantP
  ruleRec name
    = InvariantP
    . ruleRec name
    . dimap InvariantP runInvariantP

class NonTerminalSymbol a where
  nonTerminal :: String -> a
  default nonTerminal :: Typeable a => String -> a
  nonTerminal q = error (thetype ??? rexrule ??? function)
    where
      x ??? y = x <> " ??? " <> y
      thetype = show (typeRep @a)
      rexrule = "\\q{" <> q <> "}"
      function = "Control.Lens.Grammar.nonTerminal"
instance NonTerminalSymbol (RegEx c) where
  nonTerminal = NonTerminal
instance (Monoid a, NonTerminalSymbol b)
  => NonTerminalSymbol (a,b) where
    nonTerminal = pure . nonTerminal
