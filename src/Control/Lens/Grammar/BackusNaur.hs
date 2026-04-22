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
    -- * Matching
  , Matching (..)
  , diffB
  ) where

import Control.Lens
import Control.Lens.Extras
import Control.Lens.Grammar.Kleene
import Control.Lens.Grammar.Token
import Control.Lens.Grammar.Symbol
import Data.Bifunctor.Joker
import Data.Coerce
import Data.Foldable
import Data.Function
import qualified Data.IntMap.Strict as IntMap
import Data.IntMap.Strict (IntMap)
import qualified Data.IntSet as IntSet
import Data.IntSet (IntSet)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.MemoTrie
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

-- | Does a word match a pattern?
class Matching word pattern | pattern -> word where
  (=~) :: word -> pattern -> Bool
  infix 2 =~

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
      SeqEmpty -> zeroK
      NonTerminal nameY -> anyK (diff1B x) (rulesNamed nameY rules)
      Sequence y1 y2 ->
        if δ (Bnf y1 rules) then y1'y2 >|< y1y2' else y1'y2
        where
          y1'y2 = diff1B x y1 <> y2
          y1y2' = y1 <> diff1B x y2
      KleeneStar y -> diff1B x y <> starK y
      KleeneOpt y -> diff1B x y
      KleenePlus y -> diff1B x y <> starK y
      RegExam (OneOf chars) ->
        if x `elem` chars then mempty else zeroK
      RegExam (NotOneOf chars (AndAsIn cat)) ->
        if elem x chars || categorize x /= cat
          then zeroK else mempty
      RegExam (NotOneOf chars (AndNotAsIn cats)) ->
        if elem x chars || elem (categorize x) cats
          then zeroK else mempty
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

rulesNamed :: Ord rule => String -> Set (String, rule) -> Set rule
rulesNamed nameX = foldl' (flip inserter) Set.empty where
  inserter (nameY,y) =
    if nameX == nameY then Set.insert y else id

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
matchEarley word et = IntSet.member 0 acceptOrigins
  where

    initialE0 = IntMap.fromList
      [ (s, IntSet.singleton 0) | s <- IntSet.toList (earleyStartStates et) ]

    sets0 = IntMap.singleton 0 initialE0

    sets0closed = closureAt 0 sets0

    (finalSets, n) = runInput 0 sets0closed word

    runInput j ss [] = (ss, j)
    runInput j ss (x : xs) =
      let scanned = scanFrom j x ss
          ss' = IntMap.insert (j + 1) scanned ss
          closed = closureAt (j + 1) ss'
      in runInput (j + 1) closed xs

    en = IntMap.findWithDefault IntMap.empty n finalSets

    acceptOrigins = IntMap.findWithDefault IntSet.empty (earleyAcceptId et) en

    scanFrom j input ss = IntMap.foldrWithKey advance IntMap.empty e_j
      where
        e_j = IntMap.findWithDefault IntMap.empty j ss
        advance s origs acc = case IntMap.lookup s (earleyStates et) of
          Just (EarleyTerminal cls ds) | tokenClass cls input ->
            IntSet.foldr
              (\d -> IntMap.insertWith IntSet.union d origs) acc ds
          _ -> acc

    closureAt j initialSets = loop initialWork initialSets
      where
        initialE = IntMap.findWithDefault IntMap.empty j initialSets
        initialWork =
          [ (s, i) | (s, os) <- IntMap.toList initialE, i <- IntSet.toList os ]
        loop [] ss = ss
        loop ((s, i) : rest) ss = case IntMap.lookup s (earleyStates et) of
          Just (EarleyNonTerminal name ds) ->
            let (firsts, isNull) = Map.findWithDefault
                  (IntSet.empty, False) name (earleyRules et)
                predItems = [(f, j) | f <- IntSet.toList firsts]
                nullItems =
                  if isNull then [(d, i) | d <- IntSet.toList ds] else []
                (ss', new) = addEarleyItems j (predItems <> nullItems) ss
            in loop (new <> rest) ss'
          Just (EarleyEmit name) ->
            let e_i = IntMap.findWithDefault IntMap.empty i ss
                completions =
                  [ (d, i')
                  | (t, os) <- IntMap.toList e_i
                  , Just (EarleyNonTerminal n' ds) <- [IntMap.lookup t (earleyStates et)]
                  , n' == name
                  , i' <- IntSet.toList os
                  , d <- IntSet.toList ds
                  ]
                (ss', new) = addEarleyItems j completions ss
            in loop (new <> rest) ss'
          _ -> loop rest ss

    addEarleyItems j items ss = foldl' ins (ss, []) items
      where
        ins (acc, new) (state, origin) =
          let e_j = IntMap.findWithDefault IntMap.empty j acc
              os = IntMap.findWithDefault IntSet.empty state e_j
          in if IntSet.member origin os
            then (acc, new)
            else
              let e_j' = IntMap.insert state (IntSet.insert origin os) e_j
                  acc' = IntMap.insert j e_j' acc
              in (acc', (state, origin) : new)

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
  zeroK = liftBnf0 zeroK
  (>|<) = liftBnf2 (>|<)
instance (Ord rule, Monoid rule) => Monoid (Bnf rule) where
  mempty = liftBnf0 mempty
instance (Ord rule, Semigroup rule) => Semigroup (Bnf rule) where
  (<>) = liftBnf2 (<>)
instance Categorized token
  => Matching [token] (Bnf (RegEx token)) where
    word =~ bnf = matchEarley word (compileEarley bnf)
instance Categorized token
  => Matching [token] (RegEx token) where
    word =~ pattern = word =~ liftBnf0 pattern
instance Matching s (APrism s t a b) where
  word =~ pattern = is pattern word
