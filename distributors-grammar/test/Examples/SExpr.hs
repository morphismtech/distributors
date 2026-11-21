module Examples.SExpr
  ( SExpr (..)
  , sexprGrammar
  , sexprPrettyGrammar
  , sexprExamples
  ) where

import Control.Lens hiding (List)
import Control.Lens.Grammar hiding (List)
import Data.String (IsString)

-- | Abstract syntax tree for S-expressions
data SExpr
  = Atom String       -- ^ Atomic symbol
  | List [SExpr]      -- ^ List of S-expressions
  deriving stock (Eq, Ord, Show, Read)

-- Generate prisms
makePrisms ''SExpr

-- | Grammar for S-expressions
sexprGrammar :: Grammatical Char p => p SExpr SExpr
sexprGrammar = ruleRec "sexpr" $ \sexpr -> orP
  [ _Atom >? atomG
  , _List >? sexprListG sexpr
  ]
  where
    -- Atom: one or more alphanumeric or symbol characters
    atomG = rule "atom" $ someP (tokenClass atomChars)

    -- List: parenthesized sequence of S-expressions
    -- Elements are separated by whitespace
    sexprListG sexpr = rule "list" $
      terminal "(" >* sepWith " " several sexpr *< terminal ")"

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

instance CtxGrammar Char SExpr

{- | Pretty grammar for S-expressions: a list is flat, if it fits, or else
each of its elements on a line of its own, aligned after its parenthesis.
-}
sexprPrettyGrammar ::
  ( Grammatical Char p
  , forall x y. (x ~ (), y ~ ()) => Lined (p x y)
  , forall x y. (x ~ (), y ~ ()) => IsString (p x y)
  , forall x y. LaidOut (p x y)
  ) => p SExpr SExpr
sexprPrettyGrammar = ruleRec "sexpr" $ \sexpr -> orP
  [ _Atom >? rule "atom" (someP (tokenClass atomChars))
  , _List >? rule "list"
      (terminal "(" >* groupP (alignP (sepBy lineP several sexpr)) *< terminal ")")
  ]
  where
    atomChars =
      oneOf (['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ "_+-*/<>=!?")

instance PrettyGrammar SExpr where
  prettyGrammar = sexprPrettyGrammar
instance Grammar Char SExpr where grammar = sexprGrammar
