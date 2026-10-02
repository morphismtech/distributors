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
  , diffB
  ) where

import Control.Lens
import Control.Lens.Grammar.Kleene
import Control.Lens.Grammar.Token
import Control.Lens.Grammar.Symbol
import Control.Monad.Trans.Reader (ReaderT)
import Data.Bifunctor.Joker
import Data.Coerce
import Data.Function
import Data.MemoTrie
import Data.Profunctor (Star)
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
data Bnf rule start = Bnf
  { startBnf :: start
  , rulesBnf :: Set (String, rule)
  } deriving stock (Eq, Ord, Show, Read, Functor)

instance Ord rule => Applicative (Bnf rule) where
  pure start = Bnf start mempty
  liftA2 f (Bnf start0 rules0) (Bnf start1 rules1) =
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
  => [token] -> Bnf (RegEx token) (RegEx token) -> Bnf (RegEx token) (RegEx token)
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
δ :: (Categorized token, HasTrie token) => Bnf (RegEx token) (RegEx token) -> Bool
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

-- instances
instance (Ord rule, NonTerminalSymbol rule)
  => BackusNaurForm (Bnf rule rule) where
    rule label (Bnf newRule oldRules) = (nonTerminal label :: Bnf rule rule)
      {rulesBnf = Set.insert (label, newRule) oldRules}
    ruleRec label f = rule label (f (nonTerminal label))
instance (forall x. BackusNaurForm (f x))
  => BackusNaurForm (Joker f a b) where
    rule name = Joker . rule name . runJoker
    ruleRec name = Joker . ruleRec name . dimap Joker runJoker
instance BackusNaurForm (ReadP a)
instance BackusNaurForm (ReaderT r m a)
instance BackusNaurForm (Star f a b)
instance (Ord rule, TerminalSymbol token start)
  => TerminalSymbol token (Bnf rule start) where
  terminal = pure . terminal
instance (Ord rule, NonTerminalSymbol start)
  => NonTerminalSymbol (Bnf rule start) where
  nonTerminal = pure . nonTerminal
instance (Ord rule, Tokenized token start)
  => Tokenized token (Bnf rule start) where
  anyToken = pure anyToken
  token = pure . token
  oneOf = pure . oneOf
  notOneOf = pure . notOneOf
  asIn = pure . asIn
  notAsIn = pure . notAsIn
instance (Ord rule, TokenAlgebra token start)
  => TokenAlgebra token (Bnf rule start) where
  tokenClass = pure . tokenClass
instance (Ord rule, KleeneStarAlgebra start)
  => KleeneStarAlgebra (Bnf rule start) where
  starK = fmap starK
  plusK = fmap plusK
  optK = fmap optK
  zeroK = pure zeroK
  (>|<) = liftA2 (>|<)
instance (Ord rule, Monoid start) => Monoid (Bnf rule start) where
  mempty = pure mempty
instance (Ord rule, Semigroup start) => Semigroup (Bnf rule start) where
  (<>) = liftA2 (<>)
