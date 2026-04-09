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
    -- * TokenAlgebra
  , TokenAlgebra (..)
    -- * RegEx & TokenClass
  , RegEx (..)
  , TokenClass (..)
  , RegExam (..)
  , CategoryTest (..)
  ) where

import Control.Applicative
import Control.Lens.Grammar.Boole
import Control.Lens.Grammar.Symbol
import Control.Lens.Grammar.Token
import Data.Foldable
import Data.MemoTrie
import Data.Monoid
import Data.Profunctor
import Data.Profunctor.Distributor
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Generics

{- | A `KleeneStarAlgebra` is a ring
with a generally non-commutaive multiplication,
the `Monoid` concatenation operator `<>` with identity `mempty`;
and an idempotent addition, the alternation operator `>|<`
with identity `zeroK`.

It has three unary operators `optK`, `plusK` and the eponymous `starK`.

prop> starK x = optK (plusK x)
prop> plusK x = x <> starK x
prop> optK x = mempty >|< x

-}
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

-- | cumulative alternation
orK :: (Foldable f, KleeneStarAlgebra k) => f k -> k
orK = foldl' (>|<) zeroK

-- | existential
anyK :: (Foldable f, KleeneStarAlgebra k) => (a -> k) -> f a -> k
anyK f = foldl' (\b a -> b >|< f a) zeroK

-- | The `RegEx`pression type is the prototypical `KleeneStarAlgebra`.
data RegEx token
  = SeqEmpty
  | Sequence (RegEx token) (RegEx token)
  | NonTerminal String
  | KleeneStar (RegEx token)
  | KleeneOpt (RegEx token)
  | KleenePlus (RegEx token)
  | RegExam (RegExam token (RegEx token))

{- | A component of both `RegEx`pressions and `TokenClass`es,
so that the latter can be embedded in the former with `tokenClass`.
-}
data RegExam token alg
  = OneOf (Set token)
  | NotOneOf (Set token) (CategoryTest token)
  | Alternate alg alg

failExam :: RegExam token alg
failExam = OneOf Set.empty

passExam :: RegExam token alg
passExam = NotOneOf Set.empty (AndNotAsIn Set.empty)

isFailExam :: RegExam token alg -> Bool
isFailExam (OneOf xs) = Set.null xs
isFailExam _ = False

isPassExam :: RegExam token alg -> Bool
isPassExam (NotOneOf xs (AndNotAsIn ys)) = Set.null xs && Set.null ys
isPassExam _ = False

{- | `CategoryTest`s for `Categorized` tokens.-}
data CategoryTest token
  = AndAsIn (Categorize token)
  | AndNotAsIn (Set (Categorize token))

{- | `TokenClass` forms a `Tokenized` `BooleanAlgebra`,
such that the following invariants hold.

prop> trueB = anyToken
prop> notB . oneOf = notOneOf
prop> notB . notOneOf = oneOf
prop> notB . asIn = notAsIn
prop> notB . notAsIn = asIn

-}
newtype TokenClass token = TokenClass (RegExam token (TokenClass token))

-- | `TokenAlgebra` extends `Tokenized` methods to support
-- `BooleanAlgebra` operations in a `tokenClass`.
class Tokenized token p => TokenAlgebra token p where
  tokenClass :: TokenClass token -> p
  default tokenClass
    :: (p ~ q token token, Alternator q, Cochoice q)
    => TokenClass token -> p
  tokenClass (TokenClass exam) = case exam of
    OneOf chars -> oneOf chars
    NotOneOf chars (AndAsIn cat) ->
      satisfy (notOneOf chars >&&< asIn cat)
    NotOneOf chars (AndNotAsIn cats) ->
      satisfy (notOneOf chars >&&< allB notAsIn cats)
    Alternate exam1 exam2 -> tokenClass exam1 <|> tokenClass exam2

--instances
instance (Alternative f, Monoid k) => KleeneStarAlgebra (Ap f k)
deriving stock instance Generic (RegEx token)
deriving stock instance Generic (RegExam token alg)
deriving stock instance Generic1 (RegExam token)
deriving stock instance Generic (TokenClass token)
deriving stock instance Generic (CategoryTest token)
deriving stock instance Categorized token => Eq (RegEx token)
deriving stock instance Categorized token => Ord (RegEx token)
deriving stock instance
  (Categorized token, Read token, Read (Categorize token))
    => Read (RegEx token)
deriving stock instance
  (Categorized token, Show token, Show (Categorize token))
    => Show (RegEx token)
deriving stock instance
  (Categorized token, Read token, Read (Categorize token))
    => Read (TokenClass token)
deriving stock instance
  (Categorized token, Show token, Show (Categorize token))
    => Show (TokenClass token)
deriving newtype instance Categorized token => Eq (TokenClass token)
deriving newtype instance Categorized token => Ord (TokenClass token)
deriving newtype instance Categorized token => Tokenized token (TokenClass token)
deriving newtype instance Categorized token => BooleanAlgebra (TokenClass token)
instance Categorized token
  => TokenAlgebra token (TokenClass token) where
  tokenClass = id
instance Categorized token
  => TokenAlgebra token (RegExam token (TokenClass token)) where
  tokenClass (TokenClass exam) = exam
instance Categorized token => TerminalSymbol token (RegEx token) where
  terminal = foldl (\acc t -> acc <> token t) mempty
instance NonTerminalSymbol (RegEx token) where
  nonTerminal = NonTerminal
instance Categorized token => Tokenized token (RegEx token) where
  anyToken = RegExam passExam
  token a = RegExam (OneOf (Set.singleton a))
  oneOf as = RegExam (OneOf (Set.fromList (toList as)))
  notOneOf as =
    RegExam (NotOneOf (Set.fromList (toList as)) (AndNotAsIn Set.empty))
  asIn cat = RegExam (NotOneOf Set.empty (AndAsIn cat))
  notAsIn cat = RegExam (NotOneOf Set.empty (AndNotAsIn (Set.singleton cat)))
instance Categorized token => TokenAlgebra token (token -> Bool) where
  tokenClass (TokenClass exam) x = case exam of
    OneOf xs -> Set.member x xs
    NotOneOf xs (AndAsIn y) ->
      Set.notMember x xs && categorize x == y
    NotOneOf xs (AndNotAsIn ys) ->
      Set.notMember x xs && Set.notMember (categorize x) ys
    Alternate exam1 exam2 ->
      tokenClass exam1 x || tokenClass exam2 x
instance Categorized token => TokenAlgebra token (RegEx token) where
  tokenClass (TokenClass exam) = case exam of
    OneOf as -> RegExam (OneOf as)
    NotOneOf as catTest -> RegExam (NotOneOf as catTest)
    Alternate exam1 exam2 ->
      RegExam (Alternate (tokenClass exam1) (tokenClass exam2))
instance Categorized token => Monoid (RegEx token) where
  mempty = SeqEmpty
instance Categorized token => Semigroup (RegEx token) where
  SeqEmpty <> rex = rex
  rex <> SeqEmpty = rex
  RegExam exam <> _ | isFailExam exam = zeroK
  _ <> RegExam exam | isFailExam exam = zeroK
  KleeneStar rex0 <> rex1 | rex0 == rex1 = plusK rex0
  rex0 <> KleeneStar rex1 | rex0 == rex1 = plusK rex1
  rex0 <> rex1 = Sequence rex0 rex1
instance Categorized token => KleeneStarAlgebra (RegEx token) where
  zeroK = RegExam failExam
  optK (RegExam exam) | isFailExam exam = mempty
  optK SeqEmpty = mempty
  optK (KleenePlus rex) = starK rex
  optK rex = KleeneOpt rex
  starK (RegExam exam) | isFailExam exam = mempty
  starK SeqEmpty = mempty
  starK rex = KleeneStar rex
  plusK (RegExam exam) | isFailExam exam = zeroK
  plusK SeqEmpty = mempty
  plusK rex = KleenePlus rex
  KleenePlus rex >|< SeqEmpty = starK rex
  SeqEmpty >|< KleenePlus rex = starK rex
  rex >|< SeqEmpty = optK rex
  SeqEmpty >|< rex = optK rex
  rex >|< RegExam exam | isFailExam exam = rex
  RegExam exam >|< rex | isFailExam exam = rex
  rex0 >|< rex1 | Just tokenOr <- maybeOr = tokenClass tokenOr
    where
      toTokenClass (RegExam exam) =
        TokenClass <$> traverse toTokenClass exam
      toTokenClass _ = Nothing
      maybeOr = (>||<) <$> toTokenClass rex0 <*> toTokenClass rex1
  rex0 >|< rex1 | rex0 == rex1 = rex0
  rex0 >|< rex1 = RegExam (Alternate rex0 rex1)
instance Categorized token => Tokenized token (RegExam token alg) where
  anyToken = passExam
  token a = OneOf (Set.singleton a)
  oneOf as | null as = failExam
  oneOf as = OneOf (Set.fromList (toList as))
  notOneOf as | null as = passExam
  notOneOf as =
    NotOneOf (Set.fromList (toList as)) (AndNotAsIn Set.empty)
  asIn cat = NotOneOf Set.empty (AndAsIn cat)
  notAsIn cat = NotOneOf Set.empty (AndNotAsIn (Set.singleton cat))
instance Categorized token
  => BooleanAlgebra (RegExam token (TokenClass token)) where
  falseB = failExam
  trueB = passExam
  notB exam | isFailExam exam = passExam
  notB exam | isPassExam exam = failExam
  notB (Alternate (TokenClass x) (TokenClass y)) = notB x >&&< notB y
  notB (OneOf xs) = notOneOf xs
  notB (NotOneOf xs (AndAsIn y)) = oneOf xs >||< notAsIn y
  notB (NotOneOf xs (AndNotAsIn ys)) = oneOf xs >||< anyB asIn ys
  _ >&&< exam | isFailExam exam = failExam
  exam >&&< _ | isFailExam exam = failExam
  x >&&< exam | isPassExam exam = x
  exam >&&< z | isPassExam exam = z
  x >&&< Alternate (TokenClass y) (TokenClass z) = (x >&&< y) >||< (x >&&< z)
  Alternate (TokenClass x) (TokenClass y) >&&< z = (x >&&< z) >||< (y >&&< z)
  OneOf xs >&&< OneOf ys = OneOf (Set.intersection xs ys)
  OneOf xs >&&< NotOneOf ys (AndAsIn z) = OneOf
    (Set.filter (\x -> categorize x == z) (Set.difference xs ys))
  NotOneOf xs (AndAsIn y) >&&< OneOf zs = OneOf
    (Set.filter (\z -> categorize z == y) (Set.difference zs xs))
  OneOf xs >&&< NotOneOf ys (AndNotAsIn zs) = OneOf
    (Set.filter (\x -> categorize x `notElem` zs) (Set.difference xs ys))
  NotOneOf xs (AndNotAsIn ys) >&&< OneOf zs = OneOf
    (Set.filter (\z -> categorize z `notElem` ys) (Set.difference zs xs))
  NotOneOf xs (AndAsIn y) >&&< NotOneOf ws (AndAsIn z) =
    if y /= z then failExam else NotOneOf
      (Set.filter (\x -> categorize x == y) (Set.union xs ws)) (AndAsIn y)
  NotOneOf xs (AndAsIn y) >&&< NotOneOf ws (AndNotAsIn zs) =
    if y `elem` zs then failExam else NotOneOf
      (Set.filter (\x -> categorize x == y) (Set.union xs ws)) (AndAsIn y)
  NotOneOf xs (AndNotAsIn ys) >&&< NotOneOf ws (AndAsIn z) =
    if z `elem` ys then failExam else NotOneOf
      (Set.filter (\x -> categorize x == z) (Set.union xs ws)) (AndAsIn z)
  NotOneOf xs (AndNotAsIn ys) >&&< NotOneOf ws (AndNotAsIn zs) =
    let
      xws = Set.union xs ws
      yzs = Set.union ys zs
    in
      NotOneOf
        (Set.filter (\x -> categorize x `notElem` yzs) xws)
        (AndNotAsIn yzs)
  x >||< exam | isFailExam exam = x
  exam >||< y | isFailExam exam = y
  _ >||< exam | isPassExam exam = passExam
  exam >||< _ | isPassExam exam = passExam
  x >||< Alternate y z = Alternate (TokenClass x) (TokenClass (Alternate y z))
  Alternate x y >||< z = Alternate (TokenClass (Alternate x y)) (TokenClass z)
  OneOf xs >||< OneOf ys = oneOf (Set.union xs ys)
  OneOf xs >||< NotOneOf ys z =
    Alternate (TokenClass (OneOf xs)) (TokenClass (NotOneOf ys z))
  NotOneOf xs y >||< OneOf zs =
    Alternate (TokenClass (NotOneOf xs y)) (TokenClass (OneOf zs))
  NotOneOf xs (AndNotAsIn ys) >||< NotOneOf ws (AndNotAsIn zs) =
    notOneOf (Set.intersection xs ws) >&&< allB notAsIn (Set.intersection ys zs)
  NotOneOf xs (AndAsIn y) >||< NotOneOf ws (AndAsIn z) =
    if y == z then NotOneOf (Set.intersection xs ws) (AndAsIn y)
    else Alternate
      (TokenClass (NotOneOf xs (AndAsIn y)))
      (TokenClass (NotOneOf ws (AndAsIn z)))
  NotOneOf xs (AndNotAsIn ys) >||< NotOneOf ws (AndAsIn z) = Alternate
    (TokenClass (NotOneOf xs (AndNotAsIn ys)))
    (TokenClass (NotOneOf ws (AndAsIn z)))
  NotOneOf xs (AndAsIn y) >||< NotOneOf ws (AndNotAsIn zs) = Alternate
    (TokenClass (NotOneOf xs (AndAsIn y)))
    (TokenClass (NotOneOf ws (AndNotAsIn zs)))
deriving stock instance
  (Categorized token, Read token, Read alg, Read (Categorize token))
    => Read (RegExam token alg)
deriving stock instance
  (Categorized token, Show token, Show alg, Show (Categorize token))
    => Show (RegExam token alg)
deriving stock instance Functor (RegExam token)
deriving stock instance Foldable (RegExam token)
deriving stock instance Traversable (RegExam token)
deriving stock instance (Categorized token, Eq alg) => Eq (RegExam token alg)
deriving stock instance (Categorized token, Ord alg) => Ord (RegExam token alg)
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
      { epsilonTrie :: b
      , nonTerminalTrie :: String :->: b
      , sequenceTrie :: (RegEx token, RegEx token) :->: b
      , alternateTrie :: (RegEx token, RegEx token) :->: b
      , kleeneStarTrie :: RegEx token :->: b
      , kleeneOptTrie :: RegEx token :->: b
      , kleenePlusTrie :: RegEx token :->: b
      , oneOfTrie :: [token] :->: b
      , notOneOfTrie :: ([token], Either Int [Int]) :->: b
      }
    trie f = RegExTrie
      { epsilonTrie = f mempty
      , nonTerminalTrie = trie (f . nonTerminal)
      , sequenceTrie = trie (f . uncurry (<>))
      , alternateTrie = trie (f . uncurry (>|<))
      , kleeneStarTrie = trie (f . starK)
      , kleeneOptTrie = trie (f . optK)
      , kleenePlusTrie = trie (f . plusK)
      , oneOfTrie = trie (f . oneOf)
      , notOneOfTrie = trie (f . testNotOneOf)
      }
    untrie rex = \case
      SeqEmpty -> epsilonTrie rex
      NonTerminal name -> untrie (nonTerminalTrie rex) name
      Sequence x1 x2 -> untrie (sequenceTrie rex) (x1,x2)
      KleeneStar x -> untrie (kleeneStarTrie rex) x
      KleenePlus x -> untrie (kleenePlusTrie rex) x
      KleeneOpt x -> untrie (kleeneOptTrie rex) x
      RegExam (OneOf chars) -> untrie (oneOfTrie rex) (Set.toList chars)
      RegExam (NotOneOf chars (AndAsIn cat)) ->
        untrie (notOneOfTrie rex) (Set.toList chars, Left (fromEnum cat))
      RegExam (NotOneOf chars (AndNotAsIn cats)) ->
        untrie (notOneOfTrie rex)
          (Set.toList chars, Right (Set.toList (Set.map fromEnum cats)))
      RegExam (Alternate x1 x2) -> untrie (alternateTrie rex) (x1,x2)
    enumerate rex = mconcat
      [ [(SeqEmpty, epsilonTrie rex)]
      , first' NonTerminal <$> enumerate (nonTerminalTrie rex)
      , first' (uncurry Sequence) <$> enumerate (sequenceTrie rex)
      , first' (RegExam . uncurry Alternate) <$> enumerate (alternateTrie rex)
      , first' KleeneStar <$> enumerate (kleeneStarTrie rex)
      , first' KleeneOpt <$> enumerate (kleeneOptTrie rex)
      , first' KleenePlus <$> enumerate (kleenePlusTrie rex)
      , first' (RegExam . OneOf . Set.fromList) <$> enumerate (oneOfTrie rex)
      , first' testNotOneOf <$> enumerate (notOneOfTrie rex)
      ]
testNotOneOf
  :: Categorized token
  => ([token], Either Int [Int]) -> RegEx token
testNotOneOf (chars, catTest) = RegExam $ NotOneOf
  (Set.fromList chars)
  (either (AndAsIn . toEnum) (AndNotAsIn . Set.map toEnum . Set.fromList) catTest)
