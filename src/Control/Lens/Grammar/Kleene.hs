{- |
Module      : Control.Lens.Grammar.Kleene
Description : Kleene star algebras & regular expressions
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable

Regular expressions form a Kleene star algebra. See Kleene,
[Representation of Events in Nerve Nets and Finite Automata]
(https://www.rand.org/pubs/research_memoranda/RM704.html)
-}

module Control.Lens.Grammar.Kleene
  ( -- * KleeneStarAlgebra
    KleeneStarAlgebra (..)
  , orK, anyK
    -- * RegEx
  , RegEx (..)
  , RegExam (..)
  , CategoryTest (..)
  ) where

import Control.Applicative
import Control.Lens.Grammar.Symbol
import Control.Lens.Grammar.Token
import Data.Foldable
import Data.MemoTrie
import Data.Monoid
import Data.Profunctor
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Generics

class Monoid k => KleeneStarAlgebra k where
  starK, plusK, optK :: k -> k
  starK x = optK (plusK x)
  plusK x = x <> starK x
  optK x = mempty >|< x
  infixl 3 >|<
  (>|<) :: k -> k -> k
  zeroK :: k
  default (>|<) :: (k ~ f a, Alternative f) => k -> k -> k
  default zeroK :: (k ~ f a, Alternative f) => k
  (>|<) = (<|>)
  zeroK = empty

orK :: (Foldable f, KleeneStarAlgebra k) => f k -> k
orK = foldl' (>|<) zeroK

anyK :: (Foldable f, KleeneStarAlgebra k) => (a -> k) -> f a -> k
anyK f = foldl' (\b a -> b >|< f a) zeroK

data RegEx token
  = Terminal [token]
  | NonTerminal String
  | Sequence (RegEx token) (RegEx token)
  | KleeneStar (RegEx token)
  | KleeneOpt (RegEx token)
  | KleenePlus (RegEx token)
  | RegExam (RegExam token (RegEx token))

data RegExam token alg
  = Fail
  | Pass
  | OneOf (Set token)
  | NotOneOf (Set token) (CategoryTest token)
  | Alternate alg alg

data CategoryTest token
  = AsIn (Categorize token)
  | NotAsIn (Set (Categorize token))

--instances
instance (Alternative f, Monoid k) => KleeneStarAlgebra (Ap f k)
deriving stock instance Generic (RegEx token)
deriving stock instance Generic (RegExam token alg)
deriving stock instance Generic1 (RegExam token)
deriving stock instance Generic (CategoryTest token)
deriving stock instance Categorized token => Eq (RegEx token)
deriving stock instance Categorized token => Ord (RegEx token)
deriving stock instance
  (Categorized token, Read token, Read (Categorize token))
    => Read (RegEx token)
deriving stock instance
  (Categorized token, Show token, Show (Categorize token))
    => Show (RegEx token)
instance TerminalSymbol token (RegEx token) where
  terminal = Terminal . toList
instance NonTerminalSymbol (RegEx token) where
  nonTerminal = NonTerminal
instance Categorized token => Tokenized token (RegEx token) where
  anyToken = RegExam Pass
  token a = Terminal [a]
  oneOf as | null as = RegExam Fail
  oneOf as | length as == 1 = Terminal (toList as)
  oneOf as = RegExam (OneOf (foldr Set.insert Set.empty as))
  notOneOf as | null as = RegExam Pass
  notOneOf as = RegExam
    (NotOneOf (foldr Set.insert Set.empty as) (NotAsIn Set.empty))
  asIn cat = RegExam (NotOneOf Set.empty (AsIn cat))
  notAsIn cat = RegExam
    (NotOneOf Set.empty (NotAsIn (Set.singleton cat)))
instance Categorized token => Semigroup (RegEx token) where
  Terminal [] <> rex = rex
  rex <> Terminal [] = rex
  RegExam Fail <> _ = zeroK
  _ <> RegExam Fail = zeroK
  Terminal str0 <> Terminal str1 = Terminal (str0 <> str1)
  KleeneStar rex0 <> rex1
    | rex0 == rex1 = plusK rex0
  rex0 <> KleeneStar rex1
    | rex0 == rex1 = plusK rex1
  rex0 <> rex1 = Sequence rex0 rex1
instance Categorized token => Monoid (RegEx token) where
  mempty = Terminal []
instance Categorized token => KleeneStarAlgebra (RegEx token) where
  zeroK = RegExam Fail
  optK (RegExam Fail) = mempty
  optK (Terminal []) = mempty
  optK (KleenePlus rex) = starK rex
  optK rex = KleeneOpt rex
  starK (RegExam Fail) = mempty
  starK (Terminal []) = mempty
  starK rex = KleeneStar rex
  plusK (RegExam Fail) = zeroK
  plusK (Terminal []) = mempty
  plusK rex = KleenePlus rex
  KleenePlus rex >|< Terminal [] = starK rex
  Terminal [] >|< KleenePlus rex = starK rex
  rex >|< Terminal [] = optK rex
  Terminal [] >|< rex = optK rex
  rex >|< RegExam Fail = rex
  RegExam Fail >|< rex = rex
  rex0 >|< rex1 | rex0 == rex1 = rex0
  rex0 >|< rex1 = RegExam (Alternate rex0 rex1)
instance Categorized token
  => Tokenized token (RegExam token alg) where
  anyToken = Pass
  token a = OneOf (Set.singleton a)
  oneOf as | null as = Fail
  oneOf as = OneOf (Set.fromList (toList as))
  notOneOf as | null as = Pass
  notOneOf as =
    NotOneOf (Set.fromList (toList as)) (NotAsIn Set.empty)
  asIn cat = NotOneOf Set.empty (AsIn cat)
  notAsIn cat =
    NotOneOf Set.empty (NotAsIn (Set.singleton cat))
deriving stock instance
  (Categorized token, Read token, Read alg, Read (Categorize token))
    => Read (RegExam token alg)
deriving stock instance
  (Categorized token, Show token, Show alg, Show (Categorize token))
    => Show (RegExam token alg)
deriving stock instance Functor (RegExam token)
deriving stock instance Foldable (RegExam token)
deriving stock instance Traversable (RegExam token)
deriving stock instance (Categorized token, Eq alg)
  => Eq (RegExam token alg)
deriving stock instance (Categorized token, Ord alg)
  => Ord (RegExam token alg)
deriving stock instance Categorized token => Eq (CategoryTest token)
deriving stock instance Categorized token => Ord (CategoryTest token)
deriving stock instance
  (Categorized token, Read token, Read (Categorize token))
    => Read (CategoryTest token)
deriving stock instance
  (Categorized token, Show token, Show (Categorize token))
    => Show (CategoryTest token)
instance (Categorized token, HasTrie token)
  => HasTrie (RegEx token) where
    data (RegEx token :->: b) = RegExTrie
      { terminalTrie :: [token] :->: b
      , nonTerminalTrie :: String :->: b
      , sequenceTrie :: (RegEx token, RegEx token) :->: b
      , alternateTrie :: (RegEx token, RegEx token) :->: b
      , kleeneStarTrie :: RegEx token :->: b
      , kleeneOptTrie :: RegEx token :->: b
      , kleenePlusTrie :: RegEx token :->: b
      , failTrie :: b
      , passTrie :: b
      , oneOfTrie :: [token] :->: b
      , notOneOfTrie :: ([token], Either Int [Int]) :->: b
      }
    trie f = RegExTrie
      { terminalTrie = trie (f . terminal)
      , nonTerminalTrie = trie (f . nonTerminal)
      , sequenceTrie = trie (f . uncurry (<>))
      , alternateTrie = trie (f . uncurry (>|<))
      , kleeneStarTrie = trie (f . starK)
      , kleeneOptTrie = trie (f . optK)
      , kleenePlusTrie = trie (f . plusK)
      , failTrie = f zeroK
      , passTrie = f anyToken
      , oneOfTrie = trie (f . oneOf)
      , notOneOfTrie = trie (f . testNotOneOf)
      }
    untrie rex = \case
      Terminal word -> untrie (terminalTrie rex) word
      NonTerminal name -> untrie (nonTerminalTrie rex) name
      Sequence x1 x2 -> untrie (sequenceTrie rex) (x1,x2)
      KleeneStar x -> untrie (kleeneStarTrie rex) x
      KleenePlus x -> untrie (kleenePlusTrie rex) x
      KleeneOpt x -> untrie (kleeneOptTrie rex) x
      RegExam Fail -> failTrie rex
      RegExam Pass -> passTrie rex
      RegExam (OneOf chars) -> untrie (oneOfTrie rex) (Set.toList chars)
      RegExam (NotOneOf chars (AsIn cat)) ->
        untrie (notOneOfTrie rex) (Set.toList chars, Left (fromEnum cat))
      RegExam (NotOneOf chars (NotAsIn cats)) ->
        untrie (notOneOfTrie rex)
          (Set.toList chars, Right (Set.toList (Set.map fromEnum cats)))
      RegExam (Alternate x1 x2) -> untrie (alternateTrie rex) (x1,x2)
    enumerate rex = mconcat
      [ first' Terminal <$> enumerate (terminalTrie rex)
      , first' NonTerminal <$> enumerate (nonTerminalTrie rex)
      , first' (uncurry Sequence) <$> enumerate (sequenceTrie rex)
      , first' (RegExam . uncurry Alternate) <$> enumerate (alternateTrie rex)
      , first' KleeneStar <$> enumerate (kleeneStarTrie rex)
      , first' KleeneOpt <$> enumerate (kleeneOptTrie rex)
      , first' KleenePlus <$> enumerate (kleenePlusTrie rex)
      , [(RegExam Fail, failTrie rex)]
      , [(RegExam Pass, passTrie rex)]
      , first' (RegExam . OneOf . Set.fromList) <$> enumerate (oneOfTrie rex)
      , first' testNotOneOf <$> enumerate (notOneOfTrie rex)
      ]
testNotOneOf
  :: Categorized token
  => ([token], Either Int [Int]) -> RegEx token
testNotOneOf (chars, catTest) = RegExam $
  NotOneOf (Set.fromList chars) (either (AsIn . toEnum) (NotAsIn . Set.map toEnum . Set.fromList) catTest)
