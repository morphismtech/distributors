{- |
Module      : Control.Lens.Grammar.Analysis
Description : static analyses of grammars
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable

Static analyses of `RegEx`tended t'Bnf's, as generated from context-free
grammars by @Control.Lens.Grammar.regbnfG@, over any token.

A `RegEx` is the free `KleeneStarAlgebra` of token classes &
nonterminals, so an analysis which composes, like nullability or the
first tokens of a word, is the unique homomorphism out of it, `foldRegEx`,
into another `KleeneStarAlgebra`, with a least fixpoint, `fixRules`,
for the rules naming each other. An analysis which depends on context,
like the tokens which may follow a rule, flows down from its callers,
in `follows`. The @LL(1)@ conflicts, `ll1Conflicts`, are built of them.
-}

module Control.Lens.Grammar.Analysis
  ( -- * Folding
    foldRegEx
  , bnfRules
  , fixRules
    -- * Leading atoms
  , Leading (..)
  , firsts
  , firstOf
  , leftRecursive
    -- * Guards
  , Guard (..)
  , follows
    -- * LL(1)
  , ll1Conflicts
  , LL1Conflict (..)
  , LL1ConflictSort (..)
  ) where

import Control.Lens.Grammar.RegEx
import Control.Lens.Grammar.Token
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Monoid.Disjunctive
import Data.Set (Set)
import qualified Data.Set as Set

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> import Control.Lens.Grammar

{- | The homomorphism out of the free `KleeneStarAlgebra` of token
classes & nonterminals, a `RegEx`, into any other, given the
interpretations of its token classes & its nonterminals.

> prop> foldRegEx tokenClass nonTerminal = id
-}
foldRegEx
  :: KleeneStarAlgebra k
  => (TokenClass token -> k) -- ^ token classes
  -> (String -> k) -- ^ nonterminals
  -> RegEx token -> k
foldRegEx tok nonterm = go
  where
    go = \case
      SeqEmpty -> mempty
      Sequence x y zs -> mconcat (map go (x : y : zs))
      NonTerminal name -> nonterm name
      KleeneStar x -> starK (go x)
      KleeneOpt x -> optK (go x)
      KleenePlus x -> plusK (go x)
      KleeneTimes lo hi x -> timesK lo hi (go x)
      Backtracking x -> go x
      RegExam cls -> tok cls
      Alternate x y zs -> foldr1 (>|<) (map go (x : y : zs))

{- | The rules of a t'Bnf', by name,
a name's rules joined as alternatives.
-}
bnfRules :: Lexical token => Bnf (RegEx token) -> Map String (RegEx token)
bnfRules = Map.fromListWith (flip (>|<)) . Set.toList . rulesBnf

{- | The least fixpoint of an analysis of the rules of a t'Bnf',
from @bottom@, interpreting each rule's body given the analyses of the
rules it names, until they stabilize, as they do for a monotone analysis
into a lattice of finite height.
-}
fixRules
  :: (Lexical token, Eq k)
  => k -- ^ bottom
  -> (Map String k -> RegEx token -> k) -- ^ a body, given the rules
  -> Bnf (RegEx token) -> Map String k
fixRules bottom analyze bnf = go (bottom <$ rules)
  where
    rules = bnfRules bnf
    go env = let env' = analyze env <$> rules in
      if env' == env then env else go env'

{- | Whether a word can be empty, & the atoms it can lead with,
a `KleeneStarAlgebra` which, at token classes, is the first tokens of
words, & at sets of rule names, their left corners.

>>> foldRegEx (Leading False) (const falseP) ("a*b|c?" :: RegEx Char)
Leading {leadingNullable = True, leadingAtoms = fromRangeList [('a','c')]}
-}
data Leading a = Leading
  { leadingNullable :: Bool -- ^ whether a word can be empty
  , leadingAtoms :: a -- ^ the atoms a word can lead with
  } deriving stock (Eq, Ord, Show, Read)
instance DisjunctiveMonoid a => Semigroup (Leading a) where
  Leading null0 atoms0 <> Leading null1 atoms1 =
    Leading (null0 && null1) (if null0 then atoms0 >|< atoms1 else atoms0)
instance DisjunctiveMonoid a => Monoid (Leading a) where
  mempty = Leading True falseP
instance DisjunctiveMonoid a => DisjunctiveMonoid (Leading a) where
  falseP = Leading False falseP
  Leading null0 atoms0 >|< Leading null1 atoms1 =
    Leading (null0 || null1) (atoms0 >|< atoms1)
instance DisjunctiveMonoid a => KleeneStarAlgebra (Leading a) where
  starK (Leading _ atoms) = Leading True atoms
  plusK = id
  optK (Leading _ atoms) = Leading True atoms

{- | The nullability & first tokens of each rule of a t'Bnf'. -}
firsts
  :: Lexical token
  => Bnf (RegEx token) -> Map String (Leading (TokenClass token))
firsts = fixRules falseP firstOf

{- | The nullability & first tokens of a `RegEx`,
given those of the rules it names.
-}
firstOf
  :: Lexical token
  => Map String (Leading (TokenClass token))
  -> RegEx token -> Leading (TokenClass token)
firstOf rules =
  foldRegEx (Leading False) (\name -> Map.findWithDefault falseP name rules)

{- | The rules of a t'Bnf' which can name themselves
before reading a token, on which a predictive parser diverges.
-}
leftRecursive :: Lexical token => Bnf (RegEx token) -> Set String
leftRecursive bnf = Set.filter (\name -> name `Set.member` reach name) names
  where
    rules = bnfRules bnf
    names = Map.keysSet rules
    nullables = leadingNullable <$> firsts bnf
    -- the rules a body can name before reading a token
    corners = foldRegEx (const falseP) $ \name ->
      Leading (Map.findWithDefault False name nullables) (Set.singleton name)
    leftCorners = leadingAtoms . corners <$> rules
    reach name = search Set.empty (corners' name)
    corners' name = Set.toList (Map.findWithDefault Set.empty name leftCorners)
    search seen = \case
      [] -> seen
      next : rest
        | next `Set.member` seen -> search seen rest
        | otherwise -> search (Set.insert next seen) (corners' next <> rest)

{- | A guard on the next token, or the end of the input,
a `BooleanAlgebra`, by which a predictive parser decides.
The tokens which may follow a rule are a t'Guard'.
-}
data Guard token = Guard
  { guardEnd :: Bool -- ^ whether the input may end
  , guardNext :: TokenClass token -- ^ which tokens may be next
  }
deriving stock instance Lexical token => Eq (Guard token)
deriving stock instance Lexical token => Ord (Guard token)
deriving stock instance
  (Lexical token, Show (TokenTest token))
    => Show (Guard token)
instance Lexical token => DisjunctiveMonoid (Guard token) where
  falseP = Guard False falseP
  Guard end0 next0 >|< Guard end1 next1 = Guard (end0 || end1) (next0 >|< next1)
instance Lexical token => BooleanAlgebra (Guard token) where
  trueP = Guard True trueP
  notP (Guard end next) = Guard (not end) (notP next)
  Guard end0 next0 >&< Guard end1 next1 = Guard (end0 && end1) (next0 >&< next1)

-- the guard of a word, then of what follows it
guardOf
  :: Lexical token
  => Leading (TokenClass token) -> Guard token -> Guard token
guardOf (Leading nullable atoms) after
  | nullable = Guard False atoms >|< after
  | otherwise = Guard False atoms

-- each of a sequence's items, with the guard of what follows it
sequenced
  :: Lexical token
  => (RegEx token -> Leading (TokenClass token))
  -> Guard token -> [RegEx token] -> [(RegEx token, Guard token)]
sequenced first after = snd . foldr step (after, [])
  where
    step item (guard, acc) = (guardOf (first item) guard, (item, guard) : acc)

{- | The tokens which may follow each rule of a t'Bnf',
& whether its input may end, the least fixpoint of their callers'.

>>> follows ("{start} = \\q{a}b|\\q{a}\n{a} = c" :: Bnf (RegEx Char))
fromList [("a",Guard {guardEnd = True, guardNext = fromRangeList [('b','b')]})]
-}
follows :: Lexical token => Bnf (RegEx token) -> Map String (Guard token)
follows bnf = go (falseP <$ rules)
  where
    rules = bnfRules bnf
    first = firstOf (firsts bnf)
    go env = let env' = Map.unionWith (>|<) (falseP <$ rules) (callers env) in
      if env' == env then env else go env'
    callers env = Map.unionsWith (>|<) $
      followed (Guard True falseP) (startBnf bnf)
      : [ followed (Map.findWithDefault falseP name env) body
        | (name, body) <- Map.toList rules ]
    followed after = \case
      Sequence x y zs -> Map.unionsWith (>|<)
        [followed guard item | (item, guard) <- sequenced first after (x : y : zs)]
      NonTerminal name -> Map.singleton name after
      KleeneStar x -> followed (again x) x
      KleenePlus x -> followed (again x) x
      Backtracking x -> followed after x
      KleeneTimes lo hi x -> followed after (unrolled lo hi x)
      KleeneOpt x -> followed after x
      Alternate x y zs -> Map.unionsWith (>|<) (map (followed after) (x : y : zs))
      _ -> Map.empty
      where
        again x = Guard False (leadingAtoms (first x)) >|< after

{- | The conflicts which keep a `RegEx`tended t'Bnf' from being @LL(1)@,
that is, from being parsed predictively by one token of lookahead,
committing to an alternative by its first token, as
t'Data.Profunctor.Grammar.Parsector.Parsector' does.
An empty list means the grammar is @LL(1)@.

Alternatives are tried in order, so besides the usual conditions,
that alternatives start with distinct tokens & that repetitions
& options start with tokens which can't follow them,
a nullable alternative mustn't precede one which can consume tokens,
since it would succeed first, without consuming them.
Left recursion is reported too, since a predictive parser diverges on it.
A conflict which a `try` resolves isn't reported: of alternatives,
the first of which backtracks, or of a repetition which backtracks,
since a predictive parser then tries what follows anew.

>>> map conflictSort (ll1Conflicts ("{start} = ab|ac" :: Bnf (RegEx Char)))
[LL1FirstFirst]
>>> ll1Conflicts ("{start} = ab|c" :: Bnf (RegEx Char))
[]
-}
ll1Conflicts
  :: Lexical token => Bnf (RegEx token) -> [LL1Conflict token]
ll1Conflicts bnf =
  [ LL1Conflict (Just name) LL1LeftRecursion falseP (NonTerminal name)
  | name <- Set.toList (leftRecursive bnf)
  ]
  <> check Nothing (startBnf bnf) (Guard True falseP)
  <> concat
    [ check (Just name) body (Map.findWithDefault falseP name followers)
    | (name, body) <- Map.toList (bnfRules bnf)
    ]
  where
    first = firstOf (firsts bnf)
    followers = follows bnf
    nullable = leadingNullable . first
    atoms = leadingAtoms . first
    check name rex after = case rex of
      Sequence x y zs -> concat
        [check name item guard | (item, guard) <- sequenced first after (x : y : zs)]
      KleeneStar x -> repetition x <> check name x (again x)
      KleenePlus x -> repetition x <> check name x (again x)
      KleeneOpt x -> repetition x <> check name x after
      Backtracking x -> check name x after
      KleeneTimes lo hi x -> check name (unrolled lo hi x) after
      Alternate x y zs ->
        concat [alternation a b | (a, bs) <- pairs (x : y : zs), b <- bs]
        <> concatMap (\a -> check name a after) (x : y : zs)
      _ -> []
      where
        conflict sort toks = LL1Conflict name sort toks rex
        again x = Guard False (atoms x) >|< after
        overlapping toks
          | toks == falseP = []
          | otherwise = [toks]
        repetition x =
          [ conflict LL1NullableRepetition falseP | nullable x ]
          <> [ conflict LL1FirstFollow toks
             | not (tried x)
             , toks <- overlapping (atoms x >&< guardNext after) ]
        -- an alternative, & one after it
        alternation a b =
          [ conflict LL1FirstFirst toks
          | not (tried a)
          , toks <- overlapping (atoms a >&< atoms b) ]
          <> [ conflict LL1NullableAlternatives falseP
             | nullable a, nullable b ]
          <> [ conflict LL1NullableFirst (atoms b)
             | nullable a, not (nullable b), atoms b /= falseP ]
          <> [ conflict LL1FirstFollow toks
             | nullable b, not (nullable a), not (tried a)
             , toks <- overlapping (atoms a >&< guardNext after) ]
    pairs = \case
      [] -> []
      a : bs -> (a, bs) : pairs bs
    -- a pattern which backtracks, after reading tokens, by `try`
    tried = \case
      Backtracking _ -> True
      _ -> False

{- | A conflict keeping a grammar from being @LL(1)@,
in a rule, or `Nothing` for the start expression,
of a sort, with the tokens in conflict, at a subexpression.
-}
data LL1Conflict token = LL1Conflict
  { conflictRule :: Maybe String
  , conflictSort :: LL1ConflictSort
  , conflictTokens :: TokenClass token
  , conflictAt :: RegEx token
  }
deriving stock instance Lexical token => Eq (LL1Conflict token)
deriving stock instance
  (Lexical token, Show (TokenTest token))
    => Show (LL1Conflict token)

-- | Sorts of `LL1Conflict`s.
data LL1ConflictSort
  = LL1FirstFirst
  -- ^ alternatives which start with the same tokens
  | LL1FirstFollow
  -- ^ an option, repetition or nullable alternative which starts
  -- with tokens which may follow it
  | LL1NullableAlternatives
  -- ^ alternatives which both match the empty word
  | LL1NullableFirst
  -- ^ a nullable alternative before one which consumes tokens
  | LL1NullableRepetition
  -- ^ an option or repetition of a pattern which matches the empty word
  | LL1LeftRecursion
  -- ^ a rule which names itself before reading a token
  deriving stock (Eq, Ord, Show, Read, Enum, Bounded)

-- | Counts, unrolled, @x{lo,hi}@ as @lo@ times @x@ & then
-- @x*@, or @hi - lo@ nested options.
unrolled :: Lexical token => Int -> Maybe Int -> RegEx token -> RegEx token
unrolled lo hi x = mconcat (replicate lo x) <> case hi of
  Nothing -> starK x
  Just m -> foldr (\_ rest -> optK (x <> rest)) mempty [lo + 1 .. m]
