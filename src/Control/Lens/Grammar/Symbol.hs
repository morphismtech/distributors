module Control.Lens.Grammar.Symbol
  ( Terminator
  , TerminalSymbol (..)
  , NonTerminalSymbol (..)
  ) where

import Control.Lens
import Control.Lens.Internal.Equator
import Control.Lens.PartialIso
import Data.Kind
import Data.Profunctor
import Data.Profunctor.Distributor
import Type.Reflection

type Terminator :: Type -> (Type -> Type -> Type) -> Constraint
type Terminator a p =
  ( a ~ Alphabet (p () ())
  , forall x y. (x ~ (), y ~ ()) => TerminalSymbol (p x y)
  )

class TerminalSymbol p where
  type Alphabet p
  terminal :: [Alphabet p] -> p
  default terminal
    :: ( Monoidal q, Cochoice q, Equator c c q
       , q () () ~ p, Alphabet p ~ c, Eq c
       )
    => [Alphabet p] -> p
  terminal [] = oneP
  terminal (a:as) = only a ?< equate *> terminal as

instance TerminalSymbol [a] where
  type Alphabet [a] = a
  terminal = id

class NonTerminalSymbol a where
  nonTerminal :: String -> a
  default nonTerminal :: Typeable a => String -> a
  nonTerminal q = error (thetype ??? rexrule ??? function)
    where
      x ??? y = x <> " ??? " <> y
      thetype = show (typeRep @a)
      rexrule = "\\q{" <> q <> "}"
      function = "Control.Lens.Grammar.nonTerminal"
