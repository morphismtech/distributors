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
  , languageRun
  , expectedRun
  , unreachableRun
  , Transducer (..)
  , TransducerStep (..)
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
class Matching word pattern | pattern -> word where
  (=~) :: word -> pattern -> Bool
  infix 2 =~
-- instances
instance Categorized token
  => Matching [token] (Transducer token) where
    word =~ et = acceptsChart n chart
      where
        (n, chart) = prefixRun et word
instance Categorized token
  => Matching [token] (Bnf (RegEx token)) where
    word =~ bnf = word =~ transducer bnf
instance Categorized token
  => Matching [token] (RegEx token) where
    word =~ pattern = word =~ liftBnf0 pattern
instance Matching s (APrism s t a b) where
  word =~ pattern = is pattern word

{-| A `Transducer` is a tuple

@
T = (Σ, Δ, Q, I ⊆ Q, F ∈ Q, transition ⊆ Q × (Σ ∪ ∆) × Q, output ⊆ Q × ∆)
@

* @Σ@ is a (possibly infinite) set of terminal token classes, represented by `TokenClass`es.
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
  }

-- | A `TransducerStep` in a `Transducer`.
data TransducerStep token
  = TransitionTokenClass (TokenClass token) IntSet
  | TransitionNonTerminal String IntSet
  | EmitNonTerminal String

{- | Compile a `RegEx`tended `Bnf` into a `Transducer`,
using a combination of Thompson's algorithm for regular expressions
and Earley's algorithm for context-free grammars. See Jim & Mandelbaum,
[Efficient Earley Parsing with Regular Right-hand Sides]
(http://trevorjim.com/papers/ldta-2009.pdf),
and McIlroy, [Enumerating the strings of regular languages]
(https://www.cs.dartmouth.edu/~doug/nfa.pdf).

A transducer is a form of [finite state machine]
(https://www.scribd.com/doc/76189520/John-H-Conway-Regular-Algebra-and-Finite-Machines)
that can be run in various ways like `=~`, `expectedRun`, `languageRun` & `unreachableRun`.
-}
transducer :: Bnf (RegEx token) -> Transducer token
transducer (Bnf start rules) = Transducer
  { transducerRelations = IntMap.fromList allStates
  , transducerRules = Map.fromList
      [ ( n
        , ( Map.findWithDefault IntSet.empty n firstsMap
          , Map.findWithDefault False n nullMap
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
          , Map.findWithDefault False name nullMap
          )
        Sequence rex0 rex1 ->
          let
            (firsts1, states1, nextId1, bypass1) = thompson rex1 nextId dests
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
        RegExam (Alternate rex0 rex1) ->
          let
            (firsts1, states1, nextId1, bypass1) = thompson rex1 nextId dests
            (firsts0, states0, nextId0, bypass0) = thompson rex0 nextId1 dests
          in
            ( firsts0 <> firsts1
            , states0 <> states1
            , nextId0
            , bypass0 || bypass1
            )

prefixRun
  :: Categorized token
  => Transducer token
  -> [token]
  -> (Int, IntMap (IntMap IntSet))
prefixRun et word = go 0 (initialChart et) word
  where
    go j chart [] = (j, chart)
    go j chart (x : xs) =
      let scanned = scanFrom j x chart
          closed = closeChartAt et (j + 1) (IntMap.insert (j + 1) scanned chart)
      in go (j + 1) closed xs

    scanFrom j input chart = IntMap.foldrWithKey advance IntMap.empty eJ
      where
        eJ = IntMap.findWithDefault IntMap.empty j chart
        advance s origs acc = case IntMap.lookup s (transducerRelations et) of
          Just (TransitionTokenClass cls ds) | tokenClass cls input ->
            IntSet.foldr
              (\d -> IntMap.insertWith IntSet.union d origs) acc ds
          _ -> acc

{- | What token is expected next?
The scanner frontier, `expectedRun` returns the `TokenClass`
that can be scanned next after the given input prefix.
A `falseB` result means the current chart has no scanner transitions,
i.e. the prefix is a dead end for recognition.
-}
expectedRun
  :: Categorized token
  => Transducer token -> [token] {- ^ prefix -} -> TokenClass token
expectedRun et word = anyB fst (scanClassOptions et n chart)
  where
    (n, chart) = prefixRun et word

{- |
Rule names that can never be entered from the start
expression — dead productions. A non-empty result is a grammar-hygiene
warning: those rules can be deleted without changing the recognized language.
-}
unreachableRun :: Transducer token -> Set String
unreachableRun et =
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
`languageRun` lazily produces all words in a language from shortest to longest.
However since `TokenClass`es can resolve to infinite sets of tokens,
and the relevant case of `Char` tokens while not infinite is huge,
it samples tokens in an `Applicative` `TokenAlgebra`.
-}
languageRun
  :: (Applicative f, TokenAlgebra token (f token))
  => Transducer token -- ^ transducer
  -> f [[token]]
languageRun et = sequenceA (fmap sampleWord classWords)
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
  [ (cls, closeChartAt et (j + 1) (IntMap.insert (j + 1) scanned chart))
  | (cls, scanned) <- Map.toAscList grouped
  ]
  where
    grouped = IntMap.foldrWithKey advance Map.empty eJ
    eJ = IntMap.findWithDefault IntMap.empty j chart

    advance s origs acc = case IntMap.lookup s (transducerRelations et) of
      Just (TransitionTokenClass cls ds) ->
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
    loop ((s, i) : rest) chart = case IntMap.lookup s (transducerRelations et) of
      Just (TransitionNonTerminal name ds) ->
        let
          (firsts, isNull) = Map.findWithDefault
            (IntSet.empty, False) name (transducerRules et)
          predItems = [(f, j) | f <- IntSet.toList firsts]
          nullItems =
            if isNull then [(d, i) | d <- IntSet.toList ds] else []
          (chart', new) = addEarleyItems (predItems <> nullItems) chart
        in loop (new <> rest) chart'
      Just (EmitNonTerminal name) ->
        let
          eI = IntMap.findWithDefault IntMap.empty i chart
          completions =
            [ (d, i')
            | (t, os) <- IntMap.toList eI
            , Just (TransitionNonTerminal n' ds) <- [IntMap.lookup t (transducerRelations et)]
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
