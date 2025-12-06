module Control.Lens.Grammar.Kleene
  ( KleeneStarAlgebra (..)
  , orK, anyK
  , RegEx (..)
  , RegExam (..)
  , CategoryTest (..)
  , BooleanAlgebra (..)
  , fromBool
  , andB, orB, allB, anyB
  , TokenTest (..)
  , TokenAlgebra (..)
  ) where

import Control.Applicative
import Control.Lens.Grammar.Symbol
import Control.Lens.Grammar.Token
import Data.Foldable
import Data.Function (on)
import Data.MemoTrie
import Data.Monoid
import Data.Profunctor
import Data.Profunctor.Distributor
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

-- newtype RegEx token = RegEx (RegExtend token (RegEx token))

-- data RegExtend token alg
--   = Terminal [token]
--   | NonTerminal String
--   | Sequence (RegExtend token alg) (RegExtend token alg)
--   | KleeneStar (RegExtend token alg)
--   | KleeneOpt (RegExtend token alg)
--   | KleenePlus (RegExtend token alg)
--   | RegExam (RegExam token (RegExtend token alg))

data RegExam token alg
  = Fail
  | Pass
  | OneOf (Set token)
  | NotOneOf (Set token) (CategoryTest token)
  | Alternate alg alg

data CategoryTest token
  = AsIn (Categorize token)
  | NotAsIn (Set (Categorize token))

class BooleanAlgebra b where

  falseB :: b
  default falseB
    :: (b ~ f bool, BooleanAlgebra bool, Applicative f) => b
  falseB = pure falseB

  trueB :: b
  default trueB
    :: (b ~ f bool, BooleanAlgebra bool, Applicative f) => b
  trueB = pure trueB

  notB :: b -> b
  default notB
    :: (b ~ f bool, BooleanAlgebra bool, Functor f) => b -> b
  notB = fmap notB

  (>||<) :: b -> b -> b
  default (>||<)
    :: (b ~ f bool, BooleanAlgebra bool, Applicative f) => b -> b -> b
  (>||<) = liftA2 (>||<)

  (>&&<) :: b -> b -> b
  default (>&&<)
    :: (b ~ f bool, BooleanAlgebra bool, Applicative f) => b -> b -> b
  (>&&<) = liftA2 (>&&<)

fromBool :: BooleanAlgebra b => Bool -> b
fromBool = \case
  True -> trueB
  False -> falseB

andB :: (Foldable f, BooleanAlgebra b) => f b -> b
andB = foldl' (>&&<) trueB

orB :: (Foldable f, BooleanAlgebra b) => f b -> b
orB = foldl' (>||<) falseB

allB :: (Foldable f, BooleanAlgebra b) => (a -> b) -> f a -> b
allB f = foldl' (\b a -> b >&&< f a) trueB

anyB :: (Foldable f, BooleanAlgebra b) => (a -> b) -> f a -> b
anyB f = foldl' (\b a -> b >||< f a) falseB

newtype TokenTest token = TokenTest (RegExam token (TokenTest token))

class Tokenized token p => TokenAlgebra token p where
  tokenClass :: TokenTest token -> p
  default tokenClass
    :: (p ~ q token token, Alternator q, Cochoice q)
    => TokenTest token -> p
  tokenClass (TokenTest exam) = case exam of
    Fail -> empty
    Pass -> anyToken
    OneOf chars -> oneOf chars
    NotOneOf chars (AsIn cat) ->
      satisfy (notOneOf chars >&&< asIn cat)
    NotOneOf chars (NotAsIn cats) ->
      satisfy (notOneOf chars >&&< allB notAsIn cats)
    Alternate exam1 exam2 -> tokenClass exam1 <|> tokenClass exam2

--instances
instance (Alternative f, Monoid k) => KleeneStarAlgebra (Ap f k)
deriving stock instance Generic (RegEx token)
deriving stock instance Generic (RegExam token alg)
deriving stock instance Generic (TokenTest token)
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
  => TokenAlgebra token (RegEx token) where
  tokenClass (TokenTest tokenExam) = case tokenExam of
    Fail -> RegExam Fail
    Pass -> RegExam Pass
    OneOf as -> RegExam (OneOf as)
    NotOneOf as catTest -> RegExam (NotOneOf as catTest)
    Alternate exam1 exam2 ->
      RegExam (Alternate (tokenClass exam1) (tokenClass exam2))
instance BooleanAlgebra Bool where
  falseB = False
  trueB = True
  notB = not
  (>&&<) = (&&)
  (>||<) = (||)
instance BooleanAlgebra (x -> Bool)
instance (Applicative f, BooleanAlgebra bool)
  => BooleanAlgebra (Ap f bool)
deriving newtype instance Categorized token
  => BooleanAlgebra (TokenTest token)
deriving newtype instance Categorized token
  => Tokenized token (TokenTest token)
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
instance Categorized token
  => BooleanAlgebra (RegExam token (TokenTest token)) where
  falseB = Fail
  trueB = Pass
  notB Fail = Pass
  notB Pass = Fail
  notB (Alternate (TokenTest x) (TokenTest y)) = x >&&< y
  notB (OneOf xs) = NotOneOf xs (NotAsIn Set.empty)
  notB (NotOneOf xs (AsIn y)) =
    (Alternate `on` TokenTest)
      (OneOf xs)
      (NotOneOf Set.empty (NotAsIn (Set.singleton y)))
  notB (NotOneOf xs (NotAsIn ys)) =
    foldl' (Alternate `on` TokenTest)
      (OneOf xs)
      (Set.map (NotOneOf Set.empty . AsIn) ys)
  _ >&&< Fail = Fail
  Fail >&&< _ = Fail
  x >&&< Pass = x
  Pass >&&< y = y
  x >&&< Alternate (TokenTest y) (TokenTest z) = (x >&&< y) >||< (x >&&< z)
  Alternate (TokenTest x) (TokenTest y) >&&< z = (x >&&< z) >||< (y >&&< z)
  OneOf xs >&&< OneOf ys = OneOf (Set.intersection xs ys)
  OneOf xs >&&< NotOneOf ys (AsIn z) = OneOf
    (Set.filter (\x -> categorize x == z) (Set.difference xs ys))
  NotOneOf xs (AsIn y) >&&< OneOf zs = OneOf
    (Set.filter (\z -> categorize z == y) (Set.difference zs xs))
  OneOf xs >&&< NotOneOf ys (NotAsIn zs) = OneOf
    (Set.filter (\x -> categorize x `notElem` zs) (Set.difference xs ys))
  NotOneOf xs (NotAsIn ys) >&&< OneOf zs = OneOf
    (Set.filter (\z -> categorize z `notElem` ys) (Set.difference zs xs))
  NotOneOf xs (AsIn y) >&&< NotOneOf ws (AsIn z) =
    if y /= z then Fail else NotOneOf
      (Set.filter (\x -> categorize x == y)
      (Set.union xs ws)) (AsIn y)
  NotOneOf xs (AsIn y) >&&< NotOneOf ws (NotAsIn zs) =
    if y `elem` zs then Fail else NotOneOf
      (Set.filter (\x -> categorize x == y)
      (Set.union xs ws)) (AsIn y)
  NotOneOf xs (NotAsIn ys) >&&< NotOneOf ws (AsIn z) =
    if z `elem` ys then Fail else NotOneOf
      (Set.filter (\x -> categorize x == z) (Set.union xs ws))
      (AsIn z)
  NotOneOf xs (NotAsIn ys) >&&< NotOneOf ws (NotAsIn zs) =
    let
      xws = Set.union xs ws
      yzs = Set.union ys zs
    in
      NotOneOf
        (Set.filter (\x -> categorize x `notElem` yzs) xws)
        (NotAsIn yzs)
  x >||< Fail = x
  Fail >||< y = y
  _ >||< Pass = Pass
  Pass >||< _ = Pass
  x >||< Alternate y z = Alternate (TokenTest x) (TokenTest (Alternate y z))
  Alternate x y >||< z = Alternate (TokenTest (Alternate x y)) (TokenTest z)
  OneOf xs >||< OneOf ys = OneOf (Set.union xs ys)
  OneOf xs >||< NotOneOf ys z =
    Alternate (TokenTest (OneOf xs)) (TokenTest (NotOneOf ys z))
  NotOneOf xs y >||< OneOf zs =
    Alternate (TokenTest (NotOneOf xs y)) (TokenTest (OneOf zs))
  NotOneOf xs (NotAsIn ys) >||< NotOneOf ws (NotAsIn zs) =
    NotOneOf (Set.intersection xs ws) (NotAsIn (Set.intersection ys zs))
  NotOneOf xs (AsIn y) >||< NotOneOf ws (AsIn z) =
    if y == z then NotOneOf (Set.intersection xs ws) (AsIn y)
    else Alternate
      (TokenTest (NotOneOf xs (AsIn y)))
      (TokenTest (NotOneOf ws (AsIn z)))
  NotOneOf xs (NotAsIn ys) >||< NotOneOf ws (AsIn z) = Alternate
    (TokenTest (NotOneOf xs (NotAsIn ys)))
    (TokenTest (NotOneOf ws (AsIn z)))
  NotOneOf xs (AsIn y) >||< NotOneOf ws (NotAsIn zs) = Alternate
    (TokenTest (NotOneOf xs (AsIn y)))
    (TokenTest (NotOneOf ws (NotAsIn zs)))
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
deriving newtype instance Categorized token => Eq (TokenTest token)
deriving newtype instance Categorized token => Ord (TokenTest token)
deriving stock instance
  (Categorized token, Read token, Read (Categorize token))
    => Read (TokenTest token)
deriving stock instance
  (Categorized token, Show token, Show (Categorize token))
    => Show (TokenTest token)
instance (Categorized token, Enum (Categorize token), HasTrie token)
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
      [ first' terminal <$> enumerate (terminalTrie rex)
      , first' nonTerminal <$> enumerate (nonTerminalTrie rex)
      , first' (uncurry (<>)) <$> enumerate (sequenceTrie rex)
      , first' (uncurry (>|<)) <$> enumerate (alternateTrie rex)
      , first' starK <$> enumerate (kleeneStarTrie rex)
      , first' optK <$> enumerate (kleeneOptTrie rex)
      , first' plusK <$> enumerate (kleenePlusTrie rex)
      , [(zeroK, failTrie rex)]
      , [(anyToken, passTrie rex)]
      , first' oneOf <$> enumerate (oneOfTrie rex)
      , first' testNotOneOf <$> enumerate (notOneOfTrie rex)
      ]
testNotOneOf
  :: (Categorized token, Enum (Categorize token))
  => ([token], Either Int [Int]) -> RegEx token
testNotOneOf (chars, catTest) = tokenClass $
  notOneOf chars >&&<
    either (asIn . toEnum) (allB (notAsIn . toEnum)) catTest
