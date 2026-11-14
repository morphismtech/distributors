{- |
Module      : Control.Lens.Grammar.BackusNaur
Description : Backus-Naur forms & pattern matching
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable

See Naur & Backus, et al.
[Report on the Algorithmic Language ALGOL 60]
(https://softwarepreservation.computerhistory.org/ALGOL/report/Algol60_report_CACM_1960_June.pdf).
-}

module Control.Lens.Grammar.BackusNaur
  ( -- * BackusNaurForm
    BackusNaurForm (..)
  , Ruled (..), failP, ruleTyped
  , Tried (..)
    -- * Grammatical
  , RegGrammatical
  , Grammatical
  , CtxGrammatical
  ) where

import Control.Lens
import Control.Lens.Grammar.Token
import Control.Lens.Grammar.Symbol
import Control.Monad (MonadPlus)
import Data.Bifunctor.Joker
import Data.Kind (Constraint)
import Data.Profunctor.Distributor (Alternator)
import Data.Profunctor.Filtrator (Filtrator)
import Data.Function
import Data.List (intercalate, isPrefixOf)
import Data.Maybe (isNothing)
import Type.Reflection (SomeTypeRep (..), Typeable, splitApps, tyConModule, tyConName, typeRep)
import Data.Monoid.Disjunctive
import Text.ParserCombinators.ReadP (ReadP)
import Text.ParserCombinators.ReadPrec (ReadPrec)

{- | `BackusNaurForm` grammar combinators formalize traced
`rule` abstraction and general recursion with `ruleRec`,
related by this invariant.

> prop> rule label bnf = ruleRec label (\_ -> bnf)

The `BackusNaurForm` interface is reminiscent of
two distinct notions of "trace".
First as a [traced Cartesian monoidal category]
(https://ncatlab.org/nlab/show/traced+monoidal+category#in_cartesian_monoidal_categories)
which models general recursion abstractly,
and second as a `Debug.Trace.trace`-like label for `rule` abstraction.
The category @(->)@ already has a traced @(,)@-monoidal structure
in the form of `Data.Profunctor.unfirst` @=@ `Control.Arrow.loop`
or equivalently the fixpoint function `fix`,
determining the default method for a `BackusNaurForm`,
by which the invariant holds for any `Ruled` `rule`.

> prop> ruleRec label = rule label . fix

The `BackusNaurForm` interface permits overloading these methods,
and tracing them with a label.

Both context-free `Control.Lens.Grammar.Grammar`s
& `Control.Lens.Grammar.CtxGrammar`s
support the `BackusNaurForm` interface.
See Breitner, [Showcasing Applicative]
(https://www.joachim-breitner.de/blog/710-Showcasing_Applicative),
for the original interface.

-}
class Ruled bnf => BackusNaurForm bnf where

  {- | General recursion. -}
  ruleRec :: String -> (bnf -> bnf) -> bnf
  ruleRec label = rule label . fix

{- | `Ruled` grammar combinators formalize
`rule` abstraction, labeling a subgrammar,
which a `BackusNaurForm` names as a nonterminal,
& a parser may report on failure.

> prop> rule _ = id
-}
class Ruled p where

  {- | Subgrammar abstraction. -}
  rule :: String -> p -> p
  rule _ = id

-- | A nonterminal symbol to indicate a failure.
failP :: (Ruled p, DisjunctiveMonoid p) => String -> p
failP msg = rule msg falseP

{- | A `rule` for a Haskell type, like a type definition,
named by its `Typeable` type, so that each type's rule is its own.

Rule names follow a convention: a module-qualified word, like @M.N.x@,
names a definition by its qualified name, & may be displayed unqualified,
as @x@, whenever that's unambiguous. So a type's rule is named by its
fully qualified type, such as
@Data.Map.Internal.Map Data.Text.Internal.Text GHC.Types.Int@,
displayed as @Map Text Int@.
-}
ruleTyped :: forall a p. (Typeable a, Ruled (p a a)) => p a a -> p a a
ruleTyped = rule (qualifiedName (SomeTypeRep (typeRep @a)))
{-# INLINE ruleTyped #-}

-- | A type, `show`n with its type constructors qualified by their modules.
qualifiedName :: SomeTypeRep -> String
qualifiedName (SomeTypeRep rep) = case (bracketed tyCon, args) of
  (Just "List", [arg]) -> "[" <> qualifiedName arg <> "]"
  (Just "Unit", []) -> "()"
  (Just _, _ : _ : _) ->
    "(" <> intercalate "," (map qualifiedName args) <> ")"
  _ -> unwords (qualified : map typeArgument args)
  where
    (tyCon, args) = splitApps rep
    qualified = tyConModule tyCon <> "." <> tyConName tyCon
    typeArgument arg@(SomeTypeRep argRep) = case splitApps argRep of
      (argCon, _ : _) | isNothing (bracketed argCon) ->
        "(" <> qualifiedName arg <> ")"
      _ -> qualifiedName arg
    -- The constructors of lists & tuples, which bracket their arguments.
    bracketed con = case (tyConModule con, tyConName con) of
      ("GHC.Types", "List") -> Just "List"
      ("GHC.Tuple", name) | name == "Unit" || "Tuple" `isPrefixOf` name ->
        Just name
      _ -> Nothing

{- | `Tried` grammar combinators mark subgrammars to backtrack
upon failure, by `try`, in a predictive parser,
like t'Data.Profunctor.Grammar.Parsector.Parsector'.
Use `try` on a subgrammar which isn't @LL(1)@ but still is @LL(∞)@.
`try` doesn't change the language of a grammar,
so the default, for grammars which can't record it, is

> prop> try = id
-}
class Tried p where

  {- | Backtracking upon failure. -}
  try :: p -> p
  try = id

{- | The `Alternator`s of `terminal` symbols, `Tokenized` combinators
& `tokenClass`es, which are `Tried`, & run
@Control.Lens.Grammar.RegGrammar@s. -}
type RegGrammatical token p =
  ( forall x y. (x ~ (), y ~ ()) => TerminalSymbol token (p x y)
  , forall x y. (x ~ token, y ~ token) => TokenAlgebra token (p x y)
  , Alternator p
  , forall x y. Tried (p x y)
  ) :: Constraint

{- | The `RegGrammatical` `BackusNaurForm`s, which run `Grammar`s. -}
type Grammatical token p =
  ( RegGrammatical token p
  , forall x y. BackusNaurForm (p x y)
  ) :: Constraint

{- | The `Grammatical` `Filtrator`s, `MonadPlus`es & `MonadFail`s,
which run `CtxGrammar`s. -}
type CtxGrammatical token p =
  ( Grammatical token p
  , Filtrator p
  , forall x. MonadPlus (p x)
  , forall x. MonadFail (p x)
  ) :: Constraint


-- instances
instance (forall x. Ruled (f x)) => Ruled (Joker f a b) where
  rule name = Joker . rule name . runJoker
instance (forall x. BackusNaurForm (f x))
  => BackusNaurForm (Joker f a b) where
    ruleRec name = Joker . ruleRec name . dimap Joker runJoker
instance (forall x. Tried (f x)) => Tried (Joker f a b) where
  try = Joker . try . runJoker
instance Ruled (ReadP a)
instance BackusNaurForm (ReadP a)
instance Tried (ReadP a)
instance Ruled (ReadPrec a)
instance BackusNaurForm (ReadPrec a)
instance Tried (ReadPrec a)
