{- |
Module      : Control.Lens.Grammar.Machine
Description : finite-machine compilation and Earley-style matching
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable

This module presents a machine-oriented view of grammars:

1. Compile a grammar with regular right-hand sides into a finite control machine
   (`Transducer`) using a Thompson-style construction over regular expressions.
2. Run Earley-style chart recognition over that machine.
3. Derive practical products from the same engine: boolean matching,
   "expected token class" reporting, language generation, and dead-rule analysis.

The implementation follows mainstream Earley terminology (predict/scan/complete)
while adopting the transducer perspective used by Jim and Mandelbaum:

* Earley item `(q,i)` is represented as "machine state id @q@ with origin @i@"
  stored in chart set @E_j@.
* `closeChartAt` performs predict and complete to a fixed point at position @j@.
* `scanFrom`/`scanClassOptions` perform scanner steps to build @E_{j+1}@.
* `TransducerEmit` provides the "completed nonterminal" signal used by complete.

References:

* Trevor Jim and Yitzhak Mandelbaum, /Efficient Earley Parsing with Regular
  Right-hand Sides/ (LDTA 2009).
* Thompson-style NFA compilation accounts from compiler literature.
* Standard Earley algorithm presentations (state sets, origin indices,
  predictor/scanner/completer).
-}

module Control.Lens.Grammar.Machine
  (
    -- * Matching Interface
    Matching (..)

    -- * Machine Representation
  , Transducer (..)
  , TransducerState (..)

    -- * Compilation
  , compileTransducer

    -- * Machine Execution Utilities
  , languageGen
  , expectedGen
  , unreachableGen
  ) where

import Control.Lens
import Control.Lens.Extras
import Control.Lens.Grammar.BackusNaur
import Control.Lens.Grammar.Boole
import Control.Lens.Grammar.Kleene
import Control.Lens.Grammar.Token
import Data.Foldable
import qualified Data.IntMap.Strict as IntMap
import Data.IntMap.Strict (IntMap)
import qualified Data.IntSet as IntSet
import Data.IntSet (IntSet)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)

-- | Does a word match a pattern?
--
-- For grammar and regular-expression patterns in this package, matching is
-- performed by chart recognition over a compiled machine (`Transducer`).
class Matching word pattern | pattern -> word where
  (=~) :: word -> pattern -> Bool
  infix 2 =~

-- | A control state in the compiled parsing machine.
--
-- Read these constructors as machine instructions:
--
-- * `TransducerTokenClass` is a scanner transition over a terminal class.
-- * `TransducerNonTerminal` is a call site for a nonterminal.
-- * `TransducerEmit` is a completed nonterminal output used by completion.
--
-- This corresponds to the "finite control + call/return" view of parsing
-- transducers in LDTA 2009.
data TransducerState token
  = TransducerTokenClass (TokenClass token) IntSet
  | TransducerNonTerminal String IntSet
  | TransducerEmit String

-- | Finite control machine used by the Earley-style recognizer.
--
-- Formal machine view (adapted for this parser):
--
-- @
-- T = (Q, Σ, Γ, I, F, δ)
-- @
--
-- where:
--
-- * @Q@ (control states) = keys of `transducerStates`.
-- * @Σ@ (terminal alphabet) is represented intensionally by
--   `TokenClass token` labels in `TransducerTokenClass` transitions.
-- * @Γ@ (call alphabet / nonterminal symbols) = keys of `transducerRules`
--   and names carried by `TransducerNonTerminal` / `TransducerEmit`.
-- * @I@ (initial states) = `transducerStartStates`.
-- * @F@ (accepting states) = singleton `{transducerAcceptId}` for recognition.
-- * @δ@ (transition relation) is encoded by `transducerStates` constructors:
--
--   * `TransducerTokenClass cls ds` contributes terminal transitions on any
--     token matching @cls@ from the current state to each state in @ds@.
--   * `TransducerNonTerminal name ds` contributes call transitions on symbol
--     @name@ with return destinations @ds@ (used by Earley predict/complete).
--   * `TransducerEmit name` is a completion/output state for nonterminal @name@,
--     consumed by Earley completion rather than terminal scanning.
--
-- `transducerRules` is auxiliary indexing for Earley closure (entry-state set and
-- nullability per nonterminal), not an additional machine component.
data Transducer token = Transducer
  { transducerStates :: IntMap (TransducerState token) -- ^ @Q@
  , transducerRules :: Map String (IntSet, Bool) -- ^ @Γ@
  , transducerAcceptId :: Int -- ^ @F@
  , transducerStartStates :: IntSet -- ^ @I@
  }

-- | Compile a regular-right-side grammar into a parsing transducer.
--
-- Construction outline:
--
-- * Regular-expression fragments are lowered in Thompson style by `goEarley`.
-- * Each nonterminal gets a distinguished emit/final state.
-- * Concatenation/alternation/Kleene operators wire state sets and bypassability
--   (nullability) as in regular-expression automata construction.
-- * A fixed-point nullability analysis over the grammar enables null completion
--   during Earley closure.
compileTransducer :: Bnf (RegEx token) -> Transducer token
compileTransducer (Bnf start rules) = Transducer
  { transducerStates = IntMap.fromList allStates
  , transducerRules = Map.fromList
      [ ( n
        , ( Map.findWithDefault IntSet.empty n firstsMap
          , Map.findWithDefault False n nullMap
          )
        )
      | n <- Map.keys ruleMap
      ]
  , transducerAcceptId = transducerAcceptId0
  , transducerStartStates = startStates
  }

  where

    ruleMap = foldr
      (\(n, r) -> Map.insertWith (++) n [r]) Map.empty (toList rules)

    rexNullable nm = \case
      SeqEmpty -> True
      NonTerminal n -> Map.findWithDefault False n nm
      Sequence x y -> rexNullable nm x && rexNullable nm y
      KleeneStar _ -> True
      KleeneOpt _ -> True
      KleenePlus x -> rexNullable nm x
      RegExam (Alternate x y) -> rexNullable nm x || rexNullable nm y
      RegExam (OneOf _) -> False
      RegExam (NotOneOf _ _) -> False

    iterNull nm =
      let nm' = Map.mapWithKey
            (\n _ -> any (rexNullable nm) (Map.findWithDefault [] n ruleMap)) nm
      in if nm == nm' then nm else iterNull nm'

    nullMap = iterNull (Map.map (const False) ruleMap)

    ruleNames = Map.keys ruleMap

    transducerAcceptId0 = 0

    (finalMap, nextIdAfterFinals) =
      foldl' alloc (Map.empty, transducerAcceptId0 + 1) ruleNames
      where alloc (m, i) n = (Map.insert n i m, i + 1)

    finalStatesList = [(finalMap Map.! n, TransducerEmit n) | n <- ruleNames]

    (rulesStatesList, firstsMap, nextIdAfterRules) =
      foldl' compileRule ([], Map.empty, nextIdAfterFinals) (Map.toList ruleMap)
      where
        compileRule (sts, fm, nid) (name, prods) =
          let finalId = finalMap Map.! name
              (newSts, newFirsts, nid') =
                foldl' compileProd ([], IntSet.empty, nid) prods
              compileProd (s, fs, i) prod =
                let (f, st, i', _) =
                      goEarley prod i (IntSet.singleton finalId)
                in (s <> st, fs <> f, i')
          in (sts <> newSts, Map.insert name newFirsts fm, nid')

    (startFirsts, startStatesRaw, _, startBypass) =
      goEarley start nextIdAfterRules (IntSet.singleton transducerAcceptId0)

    startStates =
      startFirsts <> bypassStates startBypass (IntSet.singleton transducerAcceptId0)

    allStates = finalStatesList <> rulesStatesList <> startStatesRaw

    bypassStates True = id
    bypassStates False = const IntSet.empty

    goEarley rex nextId dests = case rex of
        SeqEmpty -> (IntSet.empty, [], nextId, True)
        NonTerminal name ->
          ( IntSet.singleton nextId
          , [(nextId, TransducerNonTerminal name dests)]
          , nextId + 1
          , Map.findWithDefault False name nullMap
          )
        Sequence rex0 rex1 ->
          let
            (firsts1, states1, nextId1, bypass1) = goEarley rex1 nextId dests
            (firsts0, states0, nextId0, bypass0) =
              goEarley rex0 nextId1 (firsts1 <> bypassStates bypass1 dests)
          in
            ( firsts0 <> bypassStates bypass0 firsts1
            , states0 <> states1
            , nextId0
            , bypass0 && bypass1
            )
        KleeneStar rex0 ->
          let
            (firsts, states, nextId', _) = goEarley rex0 nextId (firsts <> dests)
          in
            (firsts, states, nextId', True)
        KleeneOpt rex0 ->
          let
            (firsts, states, nextId', _) = goEarley rex0 nextId dests
          in
            (firsts, states, nextId', True)
        KleenePlus rex0 ->
          let
            (firsts, states, nextId', bypass) = goEarley rex0 nextId (firsts <> dests)
          in
            (firsts, states, nextId', bypass)
        RegExam (OneOf chars)
          | Set.null chars -> (IntSet.empty, [], nextId, False)
          | otherwise ->
              ( IntSet.singleton nextId
              , [(nextId, TransducerTokenClass (TokenClass (OneOf chars)) dests)]
              , nextId + 1
              , False
              )
        RegExam (NotOneOf chars catTest) ->
          ( IntSet.singleton nextId
          , [(nextId, TransducerTokenClass (TokenClass (NotOneOf chars catTest)) dests)]
          , nextId + 1
          , False
          )
        RegExam (Alternate rex0 rex1) ->
          let
            (firsts1, states1, nextId1, bypass1) = goEarley rex1 nextId dests
            (firsts0, states0, nextId0, bypass0) = goEarley rex0 nextId1 dests
          in
            ( firsts0 <> firsts1
            , states0 <> states1
            , nextId0
            , bypass0 || bypass1
            )

prefixGen
  :: Categorized token
  => Transducer token
  -> [token]
  -> (Int, IntMap (IntMap IntSet))
prefixGen et word = go 0 (initialChart et) word
  where
    go j chart [] = (j, chart)
    go j chart (x : xs) =
      let scanned = scanFrom j x chart
          closed = closeChartAt et (j + 1) (IntMap.insert (j + 1) scanned chart)
      in go (j + 1) closed xs

    scanFrom j input chart = IntMap.foldrWithKey advance IntMap.empty eJ
      where
        eJ = IntMap.findWithDefault IntMap.empty j chart
        advance s origs acc = case IntMap.lookup s (transducerStates et) of
          Just (TransducerTokenClass cls ds) | tokenClass cls input ->
            IntSet.foldr
              (\d -> IntMap.insertWith IntSet.union d origs) acc ds
          _ -> acc

{- |
Earley scanner frontier summarized as token classes.

Returns terminal classes that can be scanned next after the given input prefix.
An empty result means the current chart has no scanner transitions, i.e. the
prefix is a dead end for recognition.

This is the machine-level version of "what terminals are expected next?".
-}
expectedGen
  :: Categorized token
  => Transducer token -> [token] -> TokenClass token
expectedGen et word = anyB fst (scanClassOptions et n chart)
  where
    (n, chart) = prefixGen et word

{- |
Rule names declared in the `Bnf` that can never be entered from the start
expression — dead productions. A non-empty result is a grammar-hygiene
warning: those rules can be deleted without changing the recognized language.

Operationally, this is reachability over control states plus nonterminal calls.
-}
unreachableGen :: Transducer token -> Set String
unreachableGen et =
  Map.keysSet (transducerRules et) `Set.difference` called
  where
    called = bfs (transducerStartStates et) IntSet.empty Set.empty

    bfs frontier seen calls
      | IntSet.null fresh = calls
      | otherwise = bfs next (seen <> fresh) calls'
      where
        fresh = IntSet.difference frontier seen
        (next, calls') = IntSet.foldr step (IntSet.empty, calls) fresh

    step s (acc, cs) = case IntMap.lookup s (transducerStates et) of
      Just (TransducerTokenClass _ ds) -> (acc <> ds, cs)
      Just (TransducerNonTerminal name ds) ->
        let firsts = maybe IntSet.empty fst (Map.lookup name (transducerRules et))
        in (acc <> ds <> firsts, Set.insert name cs)
      Just (TransducerEmit _) -> (acc, cs)
      Nothing -> (acc, cs)
-- instances
instance Categorized token
  => Matching [token] (Bnf (RegEx token)) where
    word =~ bnf = acceptsChart et n chart
      where
        et = compileTransducer bnf
        (n, chart) = prefixGen et word
instance Categorized token
  => Matching [token] (RegEx token) where
    word =~ pattern = word =~ liftBnf0 pattern
instance Matching s (APrism s t a b) where
  word =~ pattern = is pattern word

{- |
Generate words recognized by a grammar machine using chart progression.

The algorithm performs a breadth-first exploration over scanner frontiers derived
from Earley sets, so words are produced by nondecreasing length.

Chart/state progression is deterministic (state id order). Token realization uses
`TokenAlgebra` and may be nondeterministic, but is always valid for the chosen
terminal class.
-}
languageGen
  :: (Applicative f, TokenAlgebra token (f token))
  => Transducer token
  -> f [[token]]
languageGen et = sequenceA (fmap sampleWord classWords)
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
          | acceptsChart et j chart =
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
      [ (s, IntSet.singleton 0) | s <- IntSet.toList (transducerStartStates et) ]

-- Accept iff (q_accept, 0) is in E_n.
acceptsChart
  :: Transducer token
  -> Int
  -> IntMap (IntMap IntSet)
  -> Bool
acceptsChart et j chart = IntSet.member 0 acceptOrigins
  where
    eJ = IntMap.findWithDefault IntMap.empty j chart
    acceptOrigins = IntMap.findWithDefault IntSet.empty (transducerAcceptId et) eJ

-- Group all scanner moves from E_j by token class; each result also carries the
-- closed successor chart at j+1.
scanClassOptions
  :: Categorized token
  => Transducer token
  -> Int
  -> IntMap (IntMap IntSet)
  -> [(TokenClass token, IntMap (IntMap IntSet))]
scanClassOptions et j chart =
  [ (cls, closeChartAt et (j + 1) (IntMap.insert (j + 1) scanned chart))
  | (cls, scanned) <- Map.toAscList grouped
  ]
  where
    grouped = IntMap.foldrWithKey advance Map.empty eJ
    eJ = IntMap.findWithDefault IntMap.empty j chart

    advance s origs acc = case IntMap.lookup s (transducerStates et) of
      Just (TransducerTokenClass cls ds) ->
        Map.insertWith (IntMap.unionWith IntSet.union) cls scanned acc
        where
          scanned = IntSet.foldr
            (\d -> IntMap.insertWith IntSet.union d origs) IntMap.empty ds
      _ -> acc

closeChartAt
  :: Transducer token
  -> Int
  -> IntMap (IntMap IntSet)
  -> IntMap (IntMap IntSet)
closeChartAt et j initialChart0 = loop initialWork initialChart0
  where
    initialEJ = IntMap.findWithDefault IntMap.empty j initialChart0
    initialWork =
      [ (s, i) | (s, os) <- IntMap.toList initialEJ, i <- IntSet.toList os ]

    -- Earley closure at E_j: apply predict/complete until fixed point.
    loop [] chart = chart
    loop ((s, i) : rest) chart = case IntMap.lookup s (transducerStates et) of
      Just (TransducerNonTerminal name ds) ->
        let
          (firsts, isNull) = Map.findWithDefault
            (IntSet.empty, False) name (transducerRules et)
          predItems = [(f, j) | f <- IntSet.toList firsts]
          nullItems =
            if isNull then [(d, i) | d <- IntSet.toList ds] else []
          (chart', new) = addEarleyItems (predItems <> nullItems) chart
        in loop (new <> rest) chart'
      Just (TransducerEmit name) ->
        let
          eI = IntMap.findWithDefault IntMap.empty i chart
          completions =
            [ (d, i')
            | (t, os) <- IntMap.toList eI
            , Just (TransducerNonTerminal n' ds) <- [IntMap.lookup t (transducerStates et)]
            , n' == name
            , i' <- IntSet.toList os
            , d <- IntSet.toList ds
            ]
          (chart', new) = addEarleyItems completions chart
        in loop (new <> rest) chart'
      _ -> loop rest chart

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
