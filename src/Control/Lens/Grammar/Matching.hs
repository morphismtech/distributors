{- |
Module      : Control.Lens.Grammar.Matching
Description : pattern matching & language generation
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable

https://www.cs.dartmouth.edu/~doug/nfa.pdf
http://trevorjim.com/papers/ldta-2009.pdf
-}

module Control.Lens.Grammar.Matching
  ( Matching (..)
  , languageGen
  , expected
  , unreachableRules
  ) where

import Control.Lens
import Control.Lens.Extras
import Control.Lens.Grammar.BackusNaur
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

-- | A state in the Earley-extended Thompson transducer for a `Bnf`.
-- @EarleyTerminal cls ds@ matches on a token class and transitions to @ds@.
-- @EarleyNonTerminal name ds@ is a call point for rule @name@; after @name@
-- completes, control flows to @ds@. @EarleyEmit name@ is the final state
-- for rule @name@ and triggers completion during Earley closure.
data EarleyState token
  = EarleyTerminal (TokenClass token) IntSet
  | EarleyNonTerminal String IntSet
  | EarleyEmit String

data EarleyTransducer token = EarleyTransducer
  { earleyStates :: IntMap (EarleyState token)
  , earleyRules :: Map String (IntSet, Bool)
  , earleyAcceptId :: Int
  , earleyStartStates :: IntSet
  }

compileEarley :: Bnf (RegEx token) -> EarleyTransducer token
compileEarley (Bnf start rules) = EarleyTransducer
  { earleyStates = IntMap.fromList allStates
  , earleyRules = Map.fromList
      [ ( n
        , ( Map.findWithDefault IntSet.empty n firstsMap
          , Map.findWithDefault False n nullMap
          )
        )
      | n <- Map.keys ruleMap
      ]
  , earleyAcceptId = earleyAcceptId0
  , earleyStartStates = startStates
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

    earleyAcceptId0 = 0

    (finalMap, nextIdAfterFinals) =
      foldl' alloc (Map.empty, earleyAcceptId0 + 1) ruleNames
      where alloc (m, i) n = (Map.insert n i m, i + 1)

    finalStatesList = [(finalMap Map.! n, EarleyEmit n) | n <- ruleNames]

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
      goEarley start nextIdAfterRules (IntSet.singleton earleyAcceptId0)

    startStates =
      startFirsts <> bypassStates startBypass (IntSet.singleton earleyAcceptId0)

    allStates = finalStatesList <> rulesStatesList <> startStatesRaw

    bypassStates True = id
    bypassStates False = const IntSet.empty

    goEarley rex nextId dests = case rex of
        SeqEmpty -> (IntSet.empty, [], nextId, True)
        NonTerminal name ->
          ( IntSet.singleton nextId
          , [(nextId, EarleyNonTerminal name dests)]
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
              , [(nextId, EarleyTerminal (TokenClass (OneOf chars)) dests)]
              , nextId + 1
              , False
              )
        RegExam (NotOneOf chars catTest) ->
          ( IntSet.singleton nextId
          , [(nextId, EarleyTerminal (TokenClass (NotOneOf chars catTest)) dests)]
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

matchEarley :: Categorized token => [token] -> EarleyTransducer token -> Bool
matchEarley word et = acceptsChart n chart et
  where (n, chart) = runEarleyPrefix word et

runEarleyPrefix
  :: Categorized token
  => [token]
  -> EarleyTransducer token
  -> (Int, IntMap (IntMap IntSet))
runEarleyPrefix word et = go 0 (initialChart et) word
  where
    go j ss [] = (j, ss)
    go j ss (x : xs) =
      let scanned = scanFrom j x ss
          closed = closeChartAt (j + 1) (IntMap.insert (j + 1) scanned ss) et
      in go (j + 1) closed xs

    scanFrom j input ss = IntMap.foldrWithKey advance IntMap.empty e_j
      where
        e_j = IntMap.findWithDefault IntMap.empty j ss
        advance s origs acc = case IntMap.lookup s (earleyStates et) of
          Just (EarleyTerminal cls ds) | tokenClass cls input ->
            IntSet.foldr
              (\d -> IntMap.insertWith IntSet.union d origs) acc ds
          _ -> acc

{- |
Token classes that could legally appear next after the given input prefix,
according to the grammar. An empty result means the prefix is a dead end —
no extension can ever be accepted. Useful for autocomplete and for
\"expected one of …\" parse errors.
-}
expected
  :: Categorized token
  => [token] -> Bnf (RegEx token) -> [TokenClass token]
expected word bnf = map fst (scanClassOptions n chart et)
  where
    et = compileEarley bnf
    (n, chart) = runEarleyPrefix word et

{- |
Rule names declared in the `Bnf` that can never be entered from the start
expression — dead productions. A non-empty result is a grammar-hygiene
warning: those rules can be deleted without changing the recognized language.
-}
unreachableRules :: Bnf (RegEx token) -> Set String
unreachableRules bnf =
  Map.keysSet (earleyRules et) `Set.difference` called
  where
    et = compileEarley bnf
    called = bfs (earleyStartStates et) IntSet.empty Set.empty

    bfs frontier seen calls
      | IntSet.null fresh = calls
      | otherwise = bfs next (seen <> fresh) calls'
      where
        fresh = IntSet.difference frontier seen
        (next, calls') = IntSet.foldr step (IntSet.empty, calls) fresh

    step s (acc, cs) = case IntMap.lookup s (earleyStates et) of
      Just (EarleyTerminal _ ds) -> (acc <> ds, cs)
      Just (EarleyNonTerminal name ds) ->
        let firsts = maybe IntSet.empty fst (Map.lookup name (earleyRules et))
        in (acc <> ds <> firsts, Set.insert name cs)
      Just (EarleyEmit _) -> (acc, cs)
      Nothing -> (acc, cs)
-- instances
instance Categorized token
  => Matching [token] (Bnf (RegEx token)) where
    word =~ bnf = matchEarley word (compileEarley bnf)
instance Categorized token
  => Matching [token] (RegEx token) where
    word =~ pattern = word =~ liftBnf0 pattern
instance Matching s (APrism s t a b) where
  word =~ pattern = is pattern word

{- |
Generate words recognized by a `Bnf` using Earley chart progression.

Chart/state progression is deterministic (state id order). Token realization is
random but always valid for the selected terminal class.
-}
languageGen
  :: (Applicative f, TokenAlgebra token (f token))
  => Bnf (RegEx token)
  -> f [[token]]
languageGen bnf = sequenceA (fmap sampleWord classWords)
  where
    et = compileEarley bnf

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
          | acceptsChart j chart et =
              if Set.member revWord seen
                then (acc, seen)
                else (revWord : acc, Set.insert revWord seen)
          | otherwise = (acc, seen)

    expand (j, revWord, chart) =
      [ (j + 1, cls : revWord, nextChart)
      | (cls, nextChart) <- scanClassOptions j chart et
      ]

initialChart
  :: EarleyTransducer token
  -> IntMap (IntMap IntSet)
initialChart et = closeChartAt 0 (IntMap.singleton 0 initialE0) et
  where
    initialE0 = IntMap.fromList
      [ (s, IntSet.singleton 0) | s <- IntSet.toList (earleyStartStates et) ]

acceptsChart
  :: Int
  -> IntMap (IntMap IntSet)
  -> EarleyTransducer token
  -> Bool
acceptsChart j chart et = IntSet.member 0 acceptOrigins
  where
    e_j = IntMap.findWithDefault IntMap.empty j chart
    acceptOrigins = IntMap.findWithDefault IntSet.empty (earleyAcceptId et) e_j

scanClassOptions
  :: Categorized token
  => Int
  -> IntMap (IntMap IntSet)
  -> EarleyTransducer token
  -> [(TokenClass token, IntMap (IntMap IntSet))]
scanClassOptions j chart et =
  [ (cls, closeChartAt (j + 1) (IntMap.insert (j + 1) scanned chart) et)
  | (cls, scanned) <- Map.toAscList grouped
  ]
  where
    grouped = IntMap.foldrWithKey advance Map.empty e_j
    e_j = IntMap.findWithDefault IntMap.empty j chart

    advance s origs acc = case IntMap.lookup s (earleyStates et) of
      Just (EarleyTerminal cls ds) ->
        Map.insertWith mergeEarleySet cls scanned acc
        where
          scanned = IntSet.foldr
            (\d -> IntMap.insertWith IntSet.union d origs) IntMap.empty ds
      _ -> acc

    mergeEarleySet = IntMap.unionWith IntSet.union

closeChartAt
  :: Int
  -> IntMap (IntMap IntSet)
  -> EarleyTransducer token
  -> IntMap (IntMap IntSet)
closeChartAt j initialChart0 et = loop initialWork initialChart0
  where
    initialE = IntMap.findWithDefault IntMap.empty j initialChart0
    initialWork =
      [ (s, i) | (s, os) <- IntMap.toList initialE, i <- IntSet.toList os ]

    loop [] chart = chart
    loop ((s, i) : rest) chart = case IntMap.lookup s (earleyStates et) of
      Just (EarleyNonTerminal name ds) ->
        let
          (firsts, isNull) = Map.findWithDefault
            (IntSet.empty, False) name (earleyRules et)
          predItems = [(f, j) | f <- IntSet.toList firsts]
          nullItems =
            if isNull then [(d, i) | d <- IntSet.toList ds] else []
          (chart', new) = addEarleyItems (predItems <> nullItems) chart
        in loop (new <> rest) chart'
      Just (EarleyEmit name) ->
        let
          e_i = IntMap.findWithDefault IntMap.empty i chart
          completions =
            [ (d, i')
            | (t, os) <- IntMap.toList e_i
            , Just (EarleyNonTerminal n' ds) <- [IntMap.lookup t (earleyStates et)]
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
            e_j = IntMap.findWithDefault IntMap.empty j acc
            os = IntMap.findWithDefault IntSet.empty state e_j
          in if IntSet.member origin os
            then (acc, new)
            else
              let
                e_j' = IntMap.insert state (IntSet.insert origin os) e_j
                acc' = IntMap.insert j e_j' acc
              in (acc', (state, origin) : new)
