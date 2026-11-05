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
  , Bnf (..)
  , liftBnf0
  , liftBnf1
  , liftBnf2
  , diffB
    -- * LL(1)
  , ll1Conflicts
  , LL1Conflict (..)
  , LL1ConflictSort (..)
  ) where

import Control.Lens
import Control.Lens.Grammar.RegEx
import Control.Lens.Grammar.Token
import Control.Lens.Grammar.Symbol
import Data.Bifunctor.Joker
import Data.Coerce
import Data.Function
import Data.MemoTrie
import Data.Monoid.Disjunctive
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Text.ParserCombinators.ReadP (ReadP)

{- | `BackusNaurForm` grammar combinators formalize traced
`rule` abstraction and general recursion with `ruleRec`,
related by this invariant.

prop> rule label bnf = ruleRec label (\_ -> bnf)

The `BackusNaurForm` interface is reminiscent of
two distinct notions of "trace".
First as a [traced Cartesian monoidal category]
(https://ncatlab.org/nlab/show/traced+monoidal+category#in_cartesian_monoidal_categories)
which models general recursion abstractly,
and second as a `Debug.Trace.trace`-like label for `rule` abstraction.
The category @(->)@ already has a traced @(,)@-monoidal structure
in the form of `Data.Profunctor.unfirst` @=@ `Control.Arrow.loop`
or equivalently the fixpoint function `fix`,
determining default methods for a `BackusNaurForm`.

prop> rule _ = id
prop> ruleRec _ = fix

The `BackusNaurForm` interface permits overloading these methods,
and tracing them with a label.

Both context-free `Control.Lens.Grammar.Grammar`s
& `Control.Lens.Grammar.CtxGrammar`s
support the `BackusNaurForm` interface.
See Breitner, [Showcasing Applicative]
(https://www.joachim-breitner.de/blog/710-Showcasing_Applicative),
for the original interface.

-}
class BackusNaurForm bnf where

  {- | Rule abstraction. -}
  rule :: String -> bnf -> bnf
  rule _ = id

  {- | General recursion. -}
  ruleRec :: String -> (bnf -> bnf) -> bnf
  ruleRec _ = fix

{- | A `Bnf` consists of a distinguished starting rule
and a set of named rules. When a `Bnf` supports `NonTerminalSymbol`s,
then it supports the `BackusNaurForm` interface
by replacing recursive calls with `nonTerminal`s.

prop> ruleRec label f = rule label (f (nonTerminal label))

-}
data Bnf rule = Bnf
  { startBnf :: rule
  , rulesBnf :: Set (String, rule)
  } deriving stock (Eq, Ord, Show, Read)

{- | Lift a rule to a `Bnf`. -}
liftBnf0 :: Ord a => a -> Bnf a
liftBnf0 a = Bnf a mempty

{- | Lift a function of rules to `Bnf`s. -}
liftBnf1 :: (Coercible a b, Ord b) => (a -> b) -> Bnf a -> Bnf b
liftBnf1 f (Bnf start rules) = Bnf (f start) (Set.map coerce rules)

{- | Lift a binary function of rules to `Bnf`s. -}
liftBnf2
  :: (Coercible a c, Coercible b c, Ord c)
  => (a -> b -> c) -> Bnf a -> Bnf b -> Bnf c
liftBnf2 f (Bnf start0 rules0) (Bnf start1 rules1) =
  Bnf (f start0 start1) (Set.map coerce rules0 <> Set.map coerce rules1)

{- |
The [Brzozowski derivative]
(https://dl.acm.org/doi/pdf/10.1145/321239.321249) of a
`RegEx`tended `Bnf`, with memoization.

prop> word =~ diffB prefix pattern = prefix <> word =~ pattern

Unfortunately, despite elegance & optimization, Brzozowski's
pattern matching algorithm is worst case exponential in grammar size.
See Might, Darais & Spiewak, [Parsing With Derivatives]
(https://matt.might.net/papers/might2011derivatives.pdf).
-}
diffB
  :: (Categorized token, HasTrie token)
  => [token] -> Bnf (RegEx token) -> Bnf (RegEx token)
diffB prefix (Bnf start rules) =
  Bnf (foldl' (flip diff1B) start prefix) rules
  where
    -- derivative wrt 1 token, memoized
    diff1B = memo2 $ \x -> \case
      SeqEmpty -> falseP
      NonTerminal nameY -> anyP (diff1B x) (rulesNamed nameY rules)
      Sequence y1 y2 ->
        if δ (Bnf y1 rules) then y1'y2 >|< y1y2' else y1'y2
        where
          y1'y2 = diff1B x y1 <> y2
          y1y2' = y1 <> diff1B x y2
      KleeneStar y -> diff1B x y <> starK y
      KleeneOpt y -> diff1B x y
      KleenePlus y -> diff1B x y <> starK y
      RegExam (OneOf chars) ->
        if x `elem` chars then mempty else falseP
      RegExam (NotOneOf chars (AndAsIn cat)) ->
        if elem x chars || categorize x /= cat
          then falseP else mempty
      RegExam (NotOneOf chars (AndNotAsIn cats)) ->
        if elem x chars || elem (categorize x) cats
          then falseP else mempty
      RegExam (Alternate y1 y2) -> diff1B x y1 >|< diff1B x y2

-- | Does a pattern match the empty word?
δ :: (Categorized token, HasTrie token)
  => Bnf (RegEx token) -> Bool
δ (Bnf start rules) = ν start where
  ν = memo $ \case
    SeqEmpty -> True
    KleeneStar _ -> True
    KleeneOpt _ -> True
    KleenePlus y -> ν y
    Sequence y1 y2 -> ν y1 && ν y2
    RegExam (Alternate y1 y2) -> ν y1 || ν y2
    NonTerminal nameY -> any ν (rulesNamed nameY rules)
    _ -> False

{- | The conflicts which keep a `RegEx`tended `Bnf` from being @LL(1)@,
that is, from being parsed predictively by one token of lookahead,
committing to an alternative by its first token, as
`Data.Profunctor.Grammar.Parsector.Parsector` does.
An empty list means the grammar is @LL(1)@.

Alternatives are tried in order, so besides the usual conditions,
that alternatives start with distinct tokens & that repetitions
& options start with tokens which can't follow them,
a nullable alternative mustn't precede one which can consume tokens,
since it would succeed first, without consuming them.
Left recursion is reported too, since a predictive parser diverges on it.

Token classes are compared by their intersections, `>&<`.
-}
ll1Conflicts
  :: Categorized token => Bnf (RegEx token) -> [LL1Conflict token]
ll1Conflicts (Bnf start ruleSet) =
  [ LL1Conflict (Just name) LL1LeftRecursion falseP (NonTerminal name)
  | name <- Map.keys rules, leftRecursive name
  ]
  <> check Nothing start (Follow True Set.empty)
  <> concat
    [ check (Just name) body (Map.findWithDefault noFollow name follows)
    | (name, body) <- Map.toList rules
    ]
  where
    rules = Map.fromListWith (flip (>|<)) (Set.toList ruleSet)
    noFollow = Follow False Set.empty
    -- least fixpoints of nullability & first tokens of rules
    (nulls, firsts) = fixpoint
      (\(ns, fs) -> (fmap (nullable ns) rules, fmap (first ns fs) rules))
      (False <$ rules, Set.empty <$ rules)
    isNullable = nullable nulls
    firstsOf = first nulls firsts
    -- least fixpoint of the tokens which may follow each rule
    follows = fixpoint
      (\fs -> Map.unionsWith (<>) $
        followed (Follow True Set.empty) start
        : [ followed (Map.findWithDefault noFollow name fs) body
          | (name, body) <- Map.toList rules ])
      (noFollow <$ rules)
    followed f = \case
      Sequence a b -> followed (after b f) a <> followed f b
      NonTerminal name -> Map.singleton name f
      KleeneStar a -> followed (Follow False (firstsOf a) <> f) a
      KleenePlus a -> followed (Follow False (firstsOf a) <> f) a
      KleeneOpt a -> followed f a
      RegExam (Alternate a b) ->
        Map.unionWith (<>) (followed f a) (followed f b)
      _ -> Map.empty
    after b f
      | isNullable b = Follow False (firstsOf b) <> f
      | otherwise = Follow False (firstsOf b)
    check name rex f = case rex of
      Sequence a b -> check name a (after b f) <> check name b f
      KleeneStar a -> repetition a <> check name a (again a)
      KleenePlus a -> repetition a <> check name a (again a)
      KleeneOpt a -> repetition a <> check name a f
      RegExam (Alternate a b) ->
        [ conflict LL1FirstFirst overlap
        | let overlap = overlapping (firstsOf a) (firstsOf b)
        , overlap /= falseP ]
        <> [ conflict LL1NullableAlternatives falseP
           | isNullable a, isNullable b ]
        <> [ conflict LL1NullableFirst (anyP TokenClass (firstsOf b))
           | isNullable a, not (isNullable b), not (Set.null (firstsOf b)) ]
        <> [ conflict LL1FirstFollow overlap
           | isNullable b, not (isNullable a)
           , let overlap = overlapping (firstsOf a) (followTokens f)
           , overlap /= falseP ]
        <> check name a f <> check name b f
      _ -> []
      where
        conflict sort toks = LL1Conflict name sort toks rex
        again a = Follow False (firstsOf a) <> f
        repetition a =
          [ conflict LL1NullableRepetition falseP | isNullable a ]
          <> [ conflict LL1FirstFollow overlap
             | let overlap = overlapping (firstsOf a) (followTokens f)
             , overlap /= falseP ]
    -- rules which can call themselves before consuming a token
    leftRecursive name = name `Set.member` reach Set.empty (leftCalls name)
    reach seen = \case
      [] -> seen
      next : rest
        | next `Set.member` seen -> reach seen rest
        | otherwise -> reach (Set.insert next seen) (leftCalls next <> rest)
    leftCalls name = maybe [] lefts (Map.lookup name rules)
    lefts = \case
      Sequence a b -> lefts a <> (if isNullable a then lefts b else [])
      NonTerminal name -> [name]
      KleeneStar a -> lefts a
      KleenePlus a -> lefts a
      KleeneOpt a -> lefts a
      RegExam (Alternate a b) -> lefts a <> lefts b
      _ -> []

nullable :: Map String Bool -> RegEx token -> Bool
nullable ns = \case
  SeqEmpty -> True
  Sequence a b -> nullable ns a && nullable ns b
  NonTerminal name -> Map.findWithDefault False name ns
  KleeneStar _ -> True
  KleeneOpt _ -> True
  KleenePlus a -> nullable ns a
  RegExam (Alternate a b) -> nullable ns a || nullable ns b
  RegExam _ -> False

-- | The first tokens of a `RegEx`, as a set of single token classes.
first
  :: Categorized token
  => Map String Bool -> Map String (Set (RegExam token (TokenClass token)))
  -> RegEx token -> Set (RegExam token (TokenClass token))
first ns fs = \case
  SeqEmpty -> Set.empty
  Sequence a b
    | nullable ns a -> first ns fs a <> first ns fs b
    | otherwise -> first ns fs a
  NonTerminal name -> Map.findWithDefault Set.empty name fs
  KleeneStar a -> first ns fs a
  KleeneOpt a -> first ns fs a
  KleenePlus a -> first ns fs a
  RegExam (Alternate a b) -> first ns fs a <> first ns fs b
  RegExam (OneOf toks) -> Set.map (OneOf . Set.singleton) toks
  RegExam (NotOneOf toks test) -> Set.singleton (NotOneOf toks test)
-- | The tokens in both of two sets of first tokens.
overlapping
  :: Categorized token
  => Set (RegExam token (TokenClass token))
  -> Set (RegExam token (TokenClass token))
  -> TokenClass token
overlapping xs ys = TokenClass $ foldl' (>|<) falseP
  [ common | x <- Set.toList xs, y <- Set.toList ys
  , let common = x >&< y, common /= falseP ]

fixpoint :: Eq a => (a -> a) -> a -> a
fixpoint f a = let a' = f a in if a' == a then a else fixpoint f a'

-- | Tokens which may follow, & whether the end of input may.
data Follow token = Follow Bool (Set (RegExam token (TokenClass token)))

followTokens :: Follow token -> Set (RegExam token (TokenClass token))
followTokens (Follow _ toks) = toks
deriving stock instance Categorized token => Eq (Follow token)
instance Categorized token => Semigroup (Follow token) where
  Follow end0 tokens0 <> Follow end1 tokens1 =
    Follow (end0 || end1) (tokens0 <> tokens1)

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
deriving stock instance Categorized token => Eq (LL1Conflict token)
deriving stock instance
  (Categorized token, Show token, Show (Categorize token))
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
  -- ^ a rule which calls itself before consuming a token
  deriving stock (Eq, Ord, Show, Read, Enum, Bounded)

rulesNamed :: Ord rule => String -> Set (String, rule) -> Set rule
rulesNamed nameX = foldl' (flip inserter) Set.empty where
  inserter (nameY,y) =
    if nameX == nameY then Set.insert y else id

-- instances
instance (Ord rule, NonTerminalSymbol rule)
  => BackusNaurForm (Bnf rule) where
    rule label (Bnf newRule oldRules) = (nonTerminal label)
      {rulesBnf = Set.insert (label, newRule) oldRules}
    ruleRec label f = rule label (f (nonTerminal label))
instance (forall x. BackusNaurForm (f x))
  => BackusNaurForm (Joker f a b) where
    rule name = Joker . rule name . runJoker
    ruleRec name = Joker . ruleRec name . dimap Joker runJoker
instance BackusNaurForm (ReadP a)
instance (Ord rule, TerminalSymbol token rule)
  => TerminalSymbol token (Bnf rule) where
  terminal = liftBnf0 . terminal
instance (Ord rule, NonTerminalSymbol rule)
  => NonTerminalSymbol (Bnf rule) where
  nonTerminal = liftBnf0 . nonTerminal
instance (Ord rule, Tokenized token rule)
  => Tokenized token (Bnf rule) where
  anyToken = liftBnf0 anyToken
  token = liftBnf0 . token
  oneOf = liftBnf0 . oneOf
  notOneOf = liftBnf0 . notOneOf
  asIn = liftBnf0 . asIn
  notAsIn = liftBnf0 . notAsIn
instance (Ord rule, TokenAlgebra token rule)
  => TokenAlgebra token (Bnf rule) where
  tokenClass = liftBnf0 . tokenClass
instance (Ord rule, KleeneStarAlgebra rule)
  => KleeneStarAlgebra (Bnf rule) where
  starK = liftBnf1 starK
  plusK = liftBnf1 plusK
  optK = liftBnf1 optK
instance (Ord rule, DisjunctiveMonoid rule)
  => DisjunctiveMonoid (Bnf rule) where
  falseP = liftBnf0 falseP
  (>|<) = liftBnf2 (>|<)
instance (Ord rule, Monoid rule) => Monoid (Bnf rule) where
  mempty = liftBnf0 mempty
instance (Ord rule, Semigroup rule) => Semigroup (Bnf rule) where
  (<>) = liftBnf2 (<>)
