module Examples.SExpr
  ( SExpr (..)
  , sexprGrammar
  , sexprExamples
  ) where

import Control.Lens hiding (List)
import Control.Lens.Grammar
import Control.Lens.Grammar.BackusNaur
import Control.Lens.Grammar.Boole
import Control.Lens.Grammar.Symbol
import Control.Lens.Grammar.Token
import Control.Lens.PartialIso hiding (List)
import Data.Profunctor.Distributor
import Data.Profunctor.Monoidal

-- | Abstract syntax tree for S-expressions
data SExpr
  = Atom String       -- ^ Atomic symbol
  | List [SExpr]      -- ^ List of S-expressions
  deriving stock (Eq, Ord, Show, Read)

-- Generate prisms
makePrisms ''SExpr

-- | Grammar for S-expressions
sexprGrammar :: Grammar Char SExpr
sexprGrammar = ruleRec "sexpr" $ \sexpr -> choiceP
  [ _Atom >? atomG
  , _List >? listG sexpr
  ]
  where
    -- Atom: one or more alphanumeric or symbol characters
    atomG = rule "atom" $ someP (tokenClass atomChars)

    -- List: parenthesized sequence of S-expressions
    -- Elements are separated by whitespace
    listG sexpr = rule "list" $
      terminal "(" >* several (sepBy (reqLike ' ')) sexpr *< terminal ")"

    -- Characters allowed in atoms: letters, digits, and symbols
    atomChars =
      oneOf (['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ "_+-*/<>=!?")

-- | Example S-expressions for testing
sexprExamples :: [(SExpr, String)]
sexprExamples =
  [ (Atom "foo", "foo")
  , (Atom "x", "x")
  , (Atom "+", "+")
  , (Atom "define", "define")
  , (List [], "()")
  , (List [Atom "foo"], "(foo)")
  , (List [Atom "foo", Atom "bar"], "(foo bar)")
  , (List [Atom "foo", List [Atom "bar", Atom "baz"]],
     "(foo (bar baz))")
  , (List [Atom "define", List [Atom "square", Atom "x"],
           List [Atom "*", Atom "x", Atom "x"]],
     "(define (square x) (* x x))")
  , (List [Atom "+", Atom "1", Atom "2"], "(+ 1 2)")
  , (List [Atom "if", Atom "test",
           List [Atom "then-branch"],
           List [Atom "else-branch"]],
     "(if test (then-branch) (else-branch))")
  ]
