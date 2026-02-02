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
(https://softwarepreservation.computerhistory.org/ALGOL/report/Algol60_report_CACM_1960_June.pdf)
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
import Control.Lens.Grammar.Boole
import Control.Lens.Grammar.Kleene
import Control.Lens.Grammar.Token
import Control.Lens.Grammar.Symbol
import Data.Coerce
import Data.Foldable
import Data.Function
import Data.MemoTrie
import qualified Data.Set as Set
import Data.Set (Set)

{- | `BackusNaurForm` grammar combinators formalize
`rule` abstraction and general recursion. Context-free
`Control.Lens.Grammar.Grammar`s support the `BackusNaurForm` interface.
-}
class BackusNaurForm bnf where

  {- | For a `BackusNaurForm` parser instance,
  `rule` can be used to detail parse errors.

  prop> rule name bnf = ruleRec name (\_ -> bnf)
  -}
  rule :: String -> bnf -> bnf
  rule _ = id

  {- | General recursion, using `ruleRec`, rules can refer to themselves. -}
  ruleRec :: String -> (bnf -> bnf) -> bnf
  ruleRec _ = fix

{- | A `Bnf` consists of a distinguished starting rule
and a set of named rules. -}
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
-}
diffB
  :: (Categorized token, HasTrie token)
  => [token] -> Bnf (RegEx token) -> Bnf (RegEx token)
diffB prefix (Bnf start rules) =
  Bnf (foldl' (flip diff1B) start prefix) rules
  where
    -- derivative wrt 1 token, memoized
    diff1B = memo2 $ \x -> \case
      Terminal [] -> zeroK
      Terminal (tokenY:streamY) ->
        if x == tokenY then terminal streamY else zeroK
      NonTerminal nameY -> anyK (diff1B x) (rulesNamed nameY rules)
      Sequence y1 y2 ->
        if δ (Bnf y1 rules) then y1'y2 >|< y1y2' else y1'y2
        where
          y1'y2 = diff1B x y1 <> y2
          y1y2' = y1 <> diff1B x y2
      KleeneStar y -> diff1B x y <> starK y
      KleeneOpt y -> diff1B x y
      KleenePlus y -> diff1B x y <> starK y
      RegExam Fail -> zeroK
      RegExam Pass -> mempty
      RegExam (OneOf chars) ->
        if x `elem` chars then mempty else zeroK
      RegExam (NotOneOf chars (AsIn cat)) ->
        if elem x chars || categorize x /= cat
          then zeroK else mempty
      RegExam (NotOneOf chars (NotAsIn cats)) ->
        if elem x chars || elem (categorize x) cats
          then zeroK else mempty
      RegExam (Alternate y1 y2) -> diff1B x y1 >|< diff1B x y2

-- | Does a pattern match the empty word?
δ :: (Categorized token, HasTrie token)
  => Bnf (RegEx token) -> Bool
δ (Bnf start rules) = ν start where
  ν = memo $ \case
    Terminal [] -> True
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

-- instances
instance (Ord rule, NonTerminalSymbol rule)
  => BackusNaurForm (Bnf rule) where
    rule name = ruleRec name . const
    ruleRec name f =
      let
        newStart = nonTerminal name
        Bnf newRule oldRules = f (Bnf newStart mempty)
        newRules = Set.insert (name, newRule) oldRules
      in
        Bnf newStart newRules
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
instance (Categorized token, HasTrie token)
  => Matching [token] (Bnf (RegEx token)) where
    (=~) word = δ . diffB word
instance (Categorized token, HasTrie token)
  => Matching [token] (RegEx token) where
    word =~ pattern = word =~ liftBnf0 pattern
instance Matching s (APrism s t a b) where
  word =~ pattern = is pattern word
