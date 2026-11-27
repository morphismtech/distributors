{- |
Module      : Control.Lens.Grammar.Machine
Description : matching & transducers
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Control.Lens.Grammar.Machine
  ( -- * Matching
    Matching (..)
    -- * Transducer
  , transducer
  , parseForest
  , languageSample
  , expectNext
  , unreachableRules
  , Transducer (..)
  , TransducerStep (..)
    -- * Chart
  , Chart
  , startChart
  , scanChart
  , scanChartMany
  , Scan
  , chartScan
  , nullScan
  , scanChartBy
  , chartExpects
  , chartAccepts
  , chartLength
  ) where

import Control.Lens
import Control.Lens.Extras
import Control.Lens.Grammar.BackusNaur
import Control.Lens.Grammar.RegEx
import Control.Lens.Grammar.Token
import Data.Foldable
import qualified Data.IntMap.Strict as IntMap
import Data.IntMap.Strict (IntMap)
import qualified Data.IntSet as IntSet
import Data.IntSet (IntSet)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Monoid.Disjunctive
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Tree (Tree (..))

-- | Does a word match a pattern?
class Matching word pattern | pattern -> word where
  (=~) :: word -> pattern -> Bool
  infix 2 =~
-- instances
instance Categorized token
  => Matching [token] (Transducer token) where
    word =~ et = maybe False chartAccepts (scanChartMany word (startChart et))
instance Categorized token
  => Matching [token] (Bnf (RegEx token)) where
    word =~ bnf = word =~ transducer bnf
instance Categorized token
  => Matching [token] (RegEx token) where
    word =~ pattern = word =~ liftBnf0 pattern
instance Matching s (APrism s t a b) where
  word =~ pattern = is pattern word

{-| A t'Transducer' is a tuple

@
T = (Σ, Δ, Q, I ⊆ Q, F ∈ Q, transition ⊆ Q × (Σ ∪ ∆) × Q, output ⊆ Q × ∆)
@

* @Σ@ is a (possibly infinite) set of terminal token classes, represented by t'TokenClass'es.
* @Δ@ is a finite set of nonterminals, represented by the key set of `transducerRules`.
* @Q@ is a set of states, which is represented by the key set of `transducerRelations`.
* @I@ are initial states represented by `transducerStarts`.
* @F@ is a final state represented by @0@.
* @transition@ is a relation represented by `transducerRelations`
  with `TransitionTokenClass` and `TransitionNonTerminal` transitions.
* @output@ is a relation represented by `transducerRelations` with `EmitNonTerminal` outputs.
-}
data Transducer token = Transducer
  { transducerRelations :: IntMap (TransducerStep token)
  , transducerRules :: Map String (IntSet, Bool)
  -- ^ an index into `transducerRelations` for nonterminals with precomputed nullability
  , transducerStarts :: IntSet
  -- ^ an index into `transducerRelations` for the starting rule
  }

-- | A `TransducerStep` in a t'Transducer'.
data TransducerStep token
  = TransitionTokenClass (TokenClass token) IntSet
  | TransitionNonTerminal String IntSet
  | EmitNonTerminal String

{- | Compile a `RegEx`tended t'Bnf' into a t'Transducer',
using a combination of Thompson's algorithm for regular expressions
and Earley's algorithm for context-free grammars. See Jim & Mandelbaum,
[Efficient Earley Parsing with Regular Right-hand Sides]
(http://trevorjim.com/papers/ldta-2009.pdf),
and McIlroy, [Enumerating the strings of regular languages]
(https://www.cs.dartmouth.edu/~doug/nfa.pdf).

A transducer is a form of finite state machine
that can be run in various ways like
`=~`, `expectNext`, `languageSample`, `parseForest` & `unreachableRules`.
-}
transducer :: Bnf (RegEx token) -> Transducer token
transducer (Bnf start rules) = Transducer
  { transducerRelations = IntMap.fromList allStates
  , transducerRules = Map.fromList
      [ ( n
        , ( Map.findWithDefault IntSet.empty n firstsMap
          , Set.member n nullSet
          )
        )
      | n <- Map.keys ruleMap
      ]
  , transducerStarts = startStates
  }

  where

    ruleMap = foldr
      (\(n, r) -> Map.insertWith (++) n [r]) Map.empty (toList rules)

    rexNullable nm = \case
      SeqEmpty -> True
      NonTerminal n -> Set.member n nm
      Sequence x y zs -> all (rexNullable nm) (x : y : zs)
      KleeneStar _ -> True
      KleeneOpt _ -> True
      KleenePlus x -> rexNullable nm x
      RegExam (Alternate x y zs) -> any (rexNullable nm) (x : y : zs)
      RegExam (OneOf _) -> False
      RegExam (NotOneOf _ _) -> False

    ruleNames = Map.keys ruleMap

    iterNull ns =
      let ns' = Set.fromList
            [ n
            | n <- ruleNames
            , any (rexNullable ns) (Map.findWithDefault [] n ruleMap)
            ]
      in if ns == ns' then ns else iterNull ns'

    nullSet = iterNull Set.empty

    transducerAcceptId0 = 0

    (finalMap, nextIdAfterFinals) =
      foldl' alloc (Map.empty, transducerAcceptId0 + 1) ruleNames
      where alloc (m, i) n = (Map.insert n i m, i + 1)

    finalStatesList = [(finalMap Map.! n, EmitNonTerminal n) | n <- ruleNames]

    (rulesStatesList, firstsMap, nextIdAfterRules) =
      foldl' compileRule ([], Map.empty, nextIdAfterFinals) (Map.toList ruleMap)
      where
        compileRule (sts, fm, nid) (name, prods) =
          let finalId = finalMap Map.! name
              (newSts, newFirsts, nid') =
                foldl' compileProd ([], IntSet.empty, nid) prods
              compileProd (s, fs, i) prod =
                let (f, st, i', _) =
                      thompson prod i (IntSet.singleton finalId)
                in (s <> st, fs <> f, i')
          in (sts <> newSts, Map.insert name newFirsts fm, nid')

    (startFirsts, startStatesRaw, _, startBypass) =
      thompson start nextIdAfterRules (IntSet.singleton transducerAcceptId0)

    startStates =
      startFirsts <> bypassStates startBypass (IntSet.singleton transducerAcceptId0)

    allStates = finalStatesList <> rulesStatesList <> startStatesRaw

    bypassStates True = id
    bypassStates False = const IntSet.empty

    thompson rex nextId dests = case rex of
        SeqEmpty -> (IntSet.empty, [], nextId, True)
        NonTerminal name ->
          ( IntSet.singleton nextId
          , [(nextId, TransitionNonTerminal name dests)]
          , nextId + 1
          , Set.member name nullSet
          )
        Sequence rex0 rex1 rexes ->
          let
            rest = case rexes of
              [] -> rex1
              rex2 : rexes' -> Sequence rex1 rex2 rexes'
            (firsts1, states1, nextId1, bypass1) = thompson rest nextId dests
            (firsts0, states0, nextId0, bypass0) =
              thompson rex0 nextId1 (firsts1 <> bypassStates bypass1 dests)
          in
            ( firsts0 <> bypassStates bypass0 firsts1
            , states0 <> states1
            , nextId0
            , bypass0 && bypass1
            )
        KleeneStar rex0 ->
          let
            (firsts, states, nextId', _) = thompson rex0 nextId (firsts <> dests)
          in
            (firsts, states, nextId', True)
        KleeneOpt rex0 ->
          let
            (firsts, states, nextId', _) = thompson rex0 nextId dests
          in
            (firsts, states, nextId', True)
        KleenePlus rex0 ->
          let
            (firsts, states, nextId', bypass) = thompson rex0 nextId (firsts <> dests)
          in
            (firsts, states, nextId', bypass)
        RegExam (OneOf chars)
          | Set.null chars -> (IntSet.empty, [], nextId, False)
          | otherwise ->
              ( IntSet.singleton nextId
              , [(nextId, TransitionTokenClass (TokenClass (OneOf chars)) dests)]
              , nextId + 1
              , False
              )
        RegExam (NotOneOf chars catTest) ->
          ( IntSet.singleton nextId
          , [(nextId, TransitionTokenClass (TokenClass (NotOneOf chars catTest)) dests)]
          , nextId + 1
          , False
          )
        RegExam (Alternate rex0 rex1 rexes) ->
          let
            rest = case rexes of
              [] -> rex1
              rex2 : rexes' -> RegExam (Alternate rex1 rex2 rexes')
            (firsts1, states1, nextId1, bypass1) = thompson rest nextId dests
            (firsts0, states0, nextId0, bypass0) = thompson rex0 nextId1 dests
          in
            ( firsts0 <> firsts1
            , states0 <> states1
            , nextId0
            , bypass0 || bypass1
            )

{- | The parse forest of a string of tokens. -}
parseForest
  :: Categorized token
  => Transducer token
  -> [token] -- ^ string
  -> ([Tree (String, Int, Int, [token])], [token])
  {- ^ parse forest & remaining unparsed tokens -}
parseForest et word = (concat (itemForests Set.empty Nothing 0 acceptedLen 0), drop acceptedLen word)
  where
    Chart _ n chart = scanChartLongest word (startChart et)
    relations = transducerRelations et
    acceptedLen = maximum (0 : [j | j <- [0 .. n], acceptsChart j chart])

    acceptedWord = take acceptedLen word
    sliceAt start end = take (end - start) (drop start acceptedWord)
    itemsAt j = IntMap.findWithDefault IntMap.empty j chart
    ruleInfo name = Map.findWithDefault (IntSet.empty, False) name (transducerRules et)

    edgesAt :: IntMap (IntMap [edge]) -> Int -> Int -> [edge]
    edgesAt table pos stateId =
      IntMap.findWithDefault [] stateId (IntMap.findWithDefault IntMap.empty pos table)

    insertEdges :: edge -> IntSet -> IntMap [edge] -> IntMap [edge]
    insertEdges edge dests acc = IntSet.foldr
      (\stateId m -> IntMap.insertWith (++) stateId [edge] m)
      acc
      dests

    scanBack = IntMap.fromList
      [ (end, backRow (end - 1) input)
      | (end, input) <- zip [1 .. acceptedLen] acceptedWord
      ]
      where
        backRow prev input = IntMap.foldrWithKey step IntMap.empty (itemsAt prev)
          where
            step prevState origins acc = case IntMap.lookup prevState relations of
              Just (TransitionTokenClass cls dests) | tokenClass cls input ->
                insertEdges (prevState, origins) dests acc
              _ -> acc

    completeBack = IntMap.fromList
      [ (split, IntMap.foldrWithKey step IntMap.empty (itemsAt split))
      | split <- [0 .. acceptedLen]
      ]
      where
        step caller origins acc = case IntMap.lookup caller relations of
          Just (TransitionNonTerminal name dests) ->
            insertEdges (caller, origins, name) dests acc
          _ -> acc

    ruleFinals = IntMap.foldrWithKey finalStates Map.empty relations
    finalStates stateId step acc = case step of
      EmitNonTerminal name -> Map.insert name stateId acc
      _ -> acc

    entryStates Nothing = transducerStarts et
    entryStates (Just name) = fst (ruleInfo name)

    ruleNullable = snd . ruleInfo

    itemForests guards entry origin end stateId
      | Set.member itemKey guards = []
      | otherwise = baseForests <> scannedForests <> completedForests
      where
        itemKey = Left (entry, origin, end, stateId)
        guards' = Set.insert itemKey guards

        baseForests
          | end == origin && IntSet.member stateId (entryStates entry) = [[]]
          | otherwise = []

        scannedForests
          | end <= origin = []
          | otherwise =
              [ forest
              | (prevState, origins) <- edgesAt scanBack end stateId
              , IntSet.member origin origins
              , let prev = end - 1
              , forest <- itemForests guards' entry origin prev prevState
              ]

        completedForests =
          [ prefix <> [subtree]
          | split <- [origin .. end]
          , (caller, origins, name) <- edgesAt completeBack split stateId
          , IntSet.member origin origins
          , prefix <- itemForests guards' entry origin split caller
          , subtree <- ruleTrees guards' name split end
          ]

    ruleTrees guards name start end
      | Set.member ruleKey guards = []
      | otherwise = nullableTrees <> derivedTrees
      where
        ruleKey = Right (name, start, end)
        guards' = Set.insert ruleKey guards

        nullableTrees
          | start == end && ruleNullable name = [Node (name, start, end, []) []]
          | otherwise = []

        derivedTrees = case Map.lookup name ruleFinals of
          Nothing -> []
          Just finalState ->
            [ Node (name, start, end, sliceAt start end) subtrees
            | subtrees <- itemForests guards' (Just name) start end finalState
            ]

{- | What token is expected next?
The scanner frontier, `expectNext` returns the t'TokenClass'
that can be scanned next after the given input prefix.
A `falseP` result means the current chart has no scanner transitions,
i.e. the prefix is a dead end for recognition.

`expectNext` scans its whole prefix each time it's run;
to ask after each token of a growing prefix, as a decoder does,
scan a t'Chart' a token at a time, by `scanChart`, & ask `chartExpects`.
-}
expectNext
  :: Categorized token
  => Transducer token -> [token] {- ^ prefix -} -> TokenClass token
expectNext et word = maybe falseP chartExpects (scanChartMany word (startChart et))

{- | The Earley chart of a prefix of tokens scanned by a t'Transducer':
the sets @E_0, …, E_n@ of Earley items, a state & the position it started
at, which the prefix @x_1 … x_n@ reaches. See Earley,
[An efficient context-free parsing algorithm]
(https://doi.org/10.1145/362007.362035).

A t'Chart' is a prefix's state of recognition, scanned incrementally,
a token at a time, by `scanChart`, which costs as much as closing one
set of items, rather than rescanning the prefix. Charts persist, so
one chart can be scanned by many different tokens, as a decoder does
to mask a vocabulary of pieces by a grammar.
-}
data Chart token = Chart (Transducer token) !Int (IntMap (IntMap IntSet))

{- | The number of tokens a t'Chart' has scanned. -}
chartLength :: Chart token -> Int
chartLength (Chart _ n _) = n

{- | The t'Chart' of the empty prefix. -}
startChart :: Transducer token -> Chart token
startChart et = Chart et 0 (initialChart et)

{- | Scan a token into a t'Chart', or fail when the prefix with it
is a dead end, which no word of the language starts with,
provided that each of the grammar's rules matches some word.
-}
scanChart :: Categorized token => token -> Chart token -> Maybe (Chart token)
scanChart x chart = scanChartBy (chartScan x chart) chart

{- | The scanner transitions out of a t'Chart''s last set of items
which a token passes. Tokens with equal t'Scan's scan a chart alike,
so a chart need be scanned once for each t'Scan', by `scanChartBy`,
rather than once for each token, as
`Control.Lens.Grammar.Decoding.allowedPieces` does.
A t'Scan' is of the chart it's taken of, & no other.
-}
newtype Scan = Scan IntSet
  deriving newtype (Eq, Ord, Show)

{- | The t'Scan' of a token, of a t'Chart'. -}
chartScan :: Categorized token => token -> Chart token -> Scan
chartScan x (Chart et j chart) = Scan (IntSet.fromDistinctAscList
  [ s
  | s <- IntMap.keys (chartAt j chart)
  , Just (TransitionTokenClass cls ds) <- [IntMap.lookup s (transducerRelations et)]
  , not (IntSet.null ds)
  , tokenClass cls x
  ])

{- | Does a t'Scan' pass no transitions, so that its token is a dead end? -}
nullScan :: Scan -> Bool
nullScan (Scan ss) = IntSet.null ss

{- | Scan a t'Chart' by a t'Scan' of it, as `scanChart` scans it by any
token of that t'Scan'. The scanned chart's closure is lazy, so that
it's only closed when it's scanned in turn, or asked of.
-}
scanChartBy :: Scan -> Chart token -> Maybe (Chart token)
scanChartBy (Scan ss) (Chart et j chart)
  | IntSet.null ss = Nothing
  | otherwise = Just (Chart et (j + 1) (scanItems et j ss chart))

-- Advance the items of the scanner states of E_j over a token,
-- to E_(j+1), & close it.
scanItems
  :: Transducer token -> Int -> IntSet -> IntMap (IntMap IntSet) -> IntMap (IntMap IntSet)
scanItems et j ss chart =
  closeChartAt et (j + 1) (IntMap.insert (j + 1) (IntSet.foldr advance IntMap.empty ss) chart)
  where
    eJ = chartAt j chart
    advance s acc = case (IntMap.lookup s (transducerRelations et), IntMap.lookup s eJ) of
      (Just (TransitionTokenClass _ ds), Just origs) ->
        IntSet.foldr (\d -> IntMap.insertWith IntSet.union d origs) acc ds
      _ -> acc

{- | Scan tokens into a t'Chart', in order, or fail at a dead end. -}
scanChartMany
  :: Categorized token => [token] -> Chart token -> Maybe (Chart token)
scanChartMany word chart0 = foldl' (\chart x -> chart >>= scanChart x) (Just chart0) word

-- Scan the longest prefix of tokens which isn't a dead end.
scanChartLongest :: Categorized token => [token] -> Chart token -> Chart token
scanChartLongest word chart = case word of
  x : xs | Just chart' <- scanChart x chart -> scanChartLongest xs chart'
  _ -> chart

{- | The t'TokenClass' of tokens which `scanChart` scans, the disjunction
of the classes of the scanner transitions out of the chart's last set.
-}
chartExpects :: Categorized token => Chart token -> TokenClass token
chartExpects (Chart et j chart) = anyP id (Set.fromList
  [ cls
  | s <- IntMap.keys (chartAt j chart)
  , Just (TransitionTokenClass cls _) <- [IntMap.lookup s (transducerRelations et)]
  ])

{- | Is a t'Chart''s prefix a word of the language? -}
chartAccepts :: Chart token -> Bool
chartAccepts (Chart _ j chart) = acceptsChart j chart

chartAt :: Int -> IntMap (IntMap IntSet) -> IntMap IntSet
chartAt = IntMap.findWithDefault IntMap.empty

{- |
Rule names that can never be entered from the start
expression — dead productions. A non-empty result is a grammar-hygiene
warning: those rules can be deleted without changing the recognized language.
-}
unreachableRules :: Transducer token -> Set String
unreachableRules et =
  Map.keysSet (transducerRules et) `Set.difference` called
  where
    called = bfs (transducerStarts et) IntSet.empty Set.empty

    bfs frontier seen calls
      | IntSet.null fresh = calls
      | otherwise = bfs next (seen <> fresh) calls'
      where
        fresh = IntSet.difference frontier seen
        (next, calls') = IntSet.foldr step (IntSet.empty, calls) fresh

    step s (acc, cs) = case IntMap.lookup s (transducerRelations et) of
      Just (TransitionTokenClass _ ds) -> (acc <> ds, cs)
      Just (TransitionNonTerminal name ds) ->
        let firsts = maybe IntSet.empty fst (Map.lookup name (transducerRules et))
        in (acc <> ds <> firsts, Set.insert name cs)
      Just (EmitNonTerminal _) -> (acc, cs)
      Nothing -> (acc, cs)

{- |
`languageSample` lazily produces all words in a language from shortest to longest.
However since t'TokenClass'es can resolve to infinite sets of tokens,
and the relevant case of `Char` tokens while not infinite is huge,
it samples tokens in an `Applicative` `TokenAlgebra`.
-}
languageSample
  :: (TokenAlgebra token (f token), Applicative f)
  => Transducer token -- ^ transducer
  -> f [[token]]
languageSample et = sequenceA (fmap sampleWord classWords)
  where

    classWords = enumerateByLength [(0, [], initialChart et)] Set.empty

    sampleWord = traverse tokenClass . reverse

    enumerateByLength [] _ = []
    enumerateByLength frontier seen =
      let
        (accepted, seen') = acceptedAtFrontier frontier seen
        next = concatMap expand frontier
      in accepted <> enumerateByLength next seen'

    acceptedAtFrontier frontier seen0 =
      let (acceptedRev, seen') = foldl' step ([], seen0) frontier
      in (reverse acceptedRev, seen')
      where
        step (acc, seen) (j, revWord, chart)
          | acceptsChart j chart =
              if Set.member revWord seen
                then (acc, seen)
                else (revWord : acc, Set.insert revWord seen)
          | otherwise = (acc, seen)

    expand (j, revWord, chart) =
      [ (j + 1, cls : revWord, nextChart)
      | (cls, nextChart) <- scanClassOptions et j chart
      ]

initialChart
  :: Transducer token
  -> IntMap (IntMap IntSet)
initialChart et = closeChartAt et 0 (IntMap.singleton 0 initialE0)
  where
    initialE0 = IntMap.fromList
      [ (s, IntSet.singleton 0) | s <- IntSet.toList (transducerStarts et) ]

-- Accept iff (q_accept, 0) is in E_n.
acceptsChart
  :: Int
  -> IntMap (IntMap IntSet)
  -> Bool
acceptsChart j chart = IntSet.member 0 acceptOrigins
  where
    eJ = IntMap.findWithDefault IntMap.empty j chart
    acceptOrigins = IntMap.findWithDefault IntSet.empty 0 eJ

-- Group all scanner moves from E_j by token class; each result also carries the
-- closed successor chart at j+1.
scanClassOptions
  :: Categorized token
  => Transducer token
  -> Int
  -> IntMap (IntMap IntSet)
  -> [(TokenClass token, IntMap (IntMap IntSet))]
scanClassOptions et j chart =
  [ (cls, scanItems et j ss chart)
  | (cls, ss) <- Map.toAscList grouped
  ]
  where
    grouped = Map.fromListWith IntSet.union
      [ (cls, IntSet.singleton s)
      | s <- IntMap.keys (chartAt j chart)
      , Just (TransitionTokenClass cls _) <- [IntMap.lookup s (transducerRelations et)]
      ]

closeChartAt
  :: Transducer token
  -> Int
  -> IntMap (IntMap IntSet)
  -> IntMap (IntMap IntSet)
closeChartAt et j initialChart0 = loop initialWork initialChart0 IntMap.empty
  where
    initialEJ = IntMap.findWithDefault IntMap.empty j initialChart0
    initialWork =
      [ (s, i) | (s, os) <- IntMap.toList initialEJ, i <- IntSet.toList os ]

    -- For fixed i < j, E_i does not change while closing E_j. Cache an index
    -- from nonterminal name to caller origins/continuations to speed completion.
    -- IntMap key: origin index i
    -- Map key: nonterminal name
    -- Value: list of (caller origins, continuation destinations)

    -- Earley closure at E_j: apply predict/complete until fixed point.
    loop [] chart _ = chart
    loop ((s, i) : rest) chart callerCache = case IntMap.lookup s (transducerRelations et) of
      Just (TransitionNonTerminal name ds) ->
        let
          (firsts, isNull) = Map.findWithDefault
            (IntSet.empty, False) name (transducerRules et)
          predItems = [(f, j) | f <- IntSet.toList firsts]
          nullItems =
            if isNull then [(d, i) | d <- IntSet.toList ds] else []
          (chart', new) = addEarleyItems (predItems <> nullItems) chart
        in loop (new <> rest) chart' callerCache
      Just (EmitNonTerminal name) ->
        let
          (ixed, callerCache') = callerEntries i chart callerCache
          callerRows = Map.findWithDefault [] name ixed
          completions =
            [ (d, i')
            | (os, ds) <- callerRows
            , i' <- IntSet.toList os
            , d <- IntSet.toList ds
            ]
          (chart', new) = addEarleyItems completions chart
        in loop (new <> rest) chart' callerCache'
      _ -> loop rest chart callerCache

    callerEntries i chart callerCache
      -- E_j mutates during closure, so do not cache index for i == j.
      | i == j = (buildCallerIndex (IntMap.findWithDefault IntMap.empty i chart), callerCache)
      | otherwise = case IntMap.lookup i callerCache of
          Just ixed -> (ixed, callerCache)
          Nothing ->
            let ixed = buildCallerIndex (IntMap.findWithDefault IntMap.empty i chart)
            in (ixed, IntMap.insert i ixed callerCache)

    buildCallerIndex eI = IntMap.foldrWithKey step Map.empty eI
      where
        step t os acc = case IntMap.lookup t (transducerRelations et) of
          Just (TransitionNonTerminal n ds) ->
            Map.insertWith (++) n [(os, ds)] acc
          _ -> acc

    addEarleyItems items chart = foldl' ins (chart, []) items
      where
        ins (acc, new) (state, origin) =
          let
            eJ = IntMap.findWithDefault IntMap.empty j acc
            os = IntMap.findWithDefault IntSet.empty state eJ
          in if IntSet.member origin os
            then (acc, new)
            else
              let
                eJ' = IntMap.insert state (IntSet.insert origin os) eJ
                acc' = IntMap.insert j eJ' acc
              in (acc', (state, origin) : new)
