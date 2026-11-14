{- |
Module      : Control.Lens.Grammar.Token
Description : lexical tokens
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Control.Lens.Grammar.Token
  ( -- * Tokenized
    Tokenized (..)
  , satisfy
  , tokens
    -- * Categorized
  , Categorized (..)
  , Ranges (..)
  , GeneralCategory (..)
    -- * TokenAlgebra
  , TokenAlgebra (..)
  , TokenClass (..)
  , foldTokenClass
  , TokenExam (..)
  , CategoryTest (..)
  ) where

import Control.Lens
import Control.Lens.PartialIso
import Control.Monad.Loops (iterateUntil)
import Data.Bifunctor.Joker
import Data.Char
import Data.Foldable
import Data.List (nub)
import Data.Profunctor
import Data.Monoid.Disjunctive
import Data.Profunctor.Distributor
import Data.Profunctor.Monoidal
import Data.Set (Set)
import qualified Data.Set as Set
import Data.RangeSet.Map (RSet)
import qualified Data.RangeSet.Map as RSet
import GHC.Exts (IsList (Item))
import qualified GHC.Exts as Exts
import qualified Text.Read as Read
import Text.Read (readPrec)
import GHC.Generics (Generic, Generic1)
import Data.Word
import Control.Monad.State (StateT, state)
import System.Random (RandomGen, Random, random, randomR)
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen (Gen)
import qualified Test.QuickCheck.Gen as Gen
import Text.ParserCombinators.ReadP (ReadP)
import qualified Text.ParserCombinators.ReadP as ReadP
import Text.ParserCombinators.ReadPrec (ReadPrec)
import qualified Text.ParserCombinators.ReadPrec as ReadPrec
import Data.Functor.Contravariant (Predicate (..))

{- | `Categorized` provides a type family `Categorize`
and a function to `categorize` tokens into disjoint categories.

>>> :kind! Categorize Char
Categorize Char :: *
= GeneralCategory

>>> categorize 'a'
LowercaseLetter
-}
class
  ( Ord token, Ord (Categorize token), Enum (Categorize token)
  , Ord (TokenSet token), DisjunctiveMonoid (TokenSet token)
  , IsList (TokenSet token), Item (TokenSet token) ~ token
  ) => Categorized token where
  type Categorize token
  type Categorize token = ()
  categorize :: token -> Categorize token
  default categorize :: Categorize token ~ () => token -> Categorize token
  categorize _ = ()

  {- | Sets of tokens, a `Set` by default, each set having one form,
  so that its `Eq` is its sets' equality; empty by `falseP`,
  unioned by `>|<`, & listed by `IsList`, in ascending order. -}
  type TokenSet token
  type TokenSet token = Set token
  {- | Is a token a member of a set? -}
  tokenMember :: token -> TokenSet token -> Bool
  default tokenMember
    :: TokenSet token ~ Set token => token -> TokenSet token -> Bool
  tokenMember = Set.member
  {- | The tokens of both sets. -}
  tokenIntersection :: TokenSet token -> TokenSet token -> TokenSet token
  default tokenIntersection
    :: TokenSet token ~ Set token
    => TokenSet token -> TokenSet token -> TokenSet token
  tokenIntersection = Set.intersection
  {- | The tokens of a set, but not of another. -}
  tokenDifference :: TokenSet token -> TokenSet token -> TokenSet token
  default tokenDifference
    :: TokenSet token ~ Set token
    => TokenSet token -> TokenSet token -> TokenSet token
  tokenDifference = Set.difference
instance Categorized Char where
  type Categorize Char = GeneralCategory
  categorize = generalCategory
  type TokenSet Char = Ranges Char
  tokenMember x (Ranges xs) = RSet.member x xs
  tokenIntersection (Ranges xs) (Ranges ys) = Ranges (RSet.intersection xs ys)
  tokenDifference (Ranges xs) (Ranges ys) = Ranges (RSet.difference xs ys)
instance Categorized Word8
instance Categorized ()

{- | Sets of enumerable tokens, by their disjoint ranges, of
[range-set-list](https://hackage.haskell.org/package/range-set-list),
each set having one form, so that its `Eq` is its sets' equality;
a `BooleanAlgebra` of bounded tokens. They `Show` & `Read` as a `Set`
does, by their tokens' list.
-}
newtype Ranges token = Ranges (RSet token)
  deriving newtype (Eq, Ord)
instance (Ord token, Enum token) => IsList (Ranges token) where
  type Item (Ranges token) = token
  fromList = Ranges . RSet.fromList
  toList (Ranges xs) = RSet.toList xs
instance AsEmpty (Ranges token) where
  _Empty = nearly (Ranges RSet.empty) (\(Ranges xs) -> RSet.null xs)
instance (Ord token, Enum token) => DisjunctiveMonoid (Ranges token) where
  falseP = Ranges RSet.empty
  Ranges xs >|< Ranges ys = Ranges (RSet.union xs ys)
instance (Ord token, Enum token, Bounded token)
  => BooleanAlgebra (Ranges token) where
    trueP = Ranges RSet.full
    notP (Ranges xs) = Ranges (RSet.complement xs)
    Ranges xs >&< Ranges ys = Ranges (RSet.intersection xs ys)
instance (Ord token, Enum token, Show token) => Show (Ranges token) where
  showsPrec d xs = showParen (d > 10) $
    showString "fromList " . shows (Exts.toList xs)
instance (Ord token, Enum token, Read token) => Read (Ranges token) where
  readPrec = Read.parens $ ReadPrec.prec 10 $ do
    Read.Ident "fromList" <- Read.lexP
    Exts.fromList <$> ReadPrec.step readPrec

{- | `Tokenized` combinators for constructing lexical tokens. -}
class Categorized token => Tokenized token p | p -> token where
  {- | Any single token. -}
  anyToken :: p

  {- | A single specified `token`. -}
  token :: token -> p
  default token
    :: (p ~ q token token, Choice q, Cochoice q)
    => token -> p
  token = satisfy . token

  {- | A single token which is `oneOf` a set.

  > prop> token x = oneOf [x]
  
  -}
  oneOf :: Foldable f => f token -> p
  default oneOf
    :: (p ~ q token token, Choice q, Cochoice q, Foldable f)
    => f token -> p
  oneOf = satisfy . oneOf

  {- | A single token which is `notOneOf` a set.
  
  > prop> anyToken = notOneOf []
  
  -}
  notOneOf :: Foldable f => f token -> p
  default notOneOf
    :: (p ~ q token token, Choice q, Cochoice q, Foldable f)
    => f token -> p
  notOneOf = satisfy . notOneOf

  {- | A single token which is `asIn` a category. -}
  asIn :: Categorize token -> p
  default asIn
    :: (p ~ q token token, Choice q, Cochoice q)
    => Categorize token -> p
  asIn = satisfy . asIn

  {- | A single token which is `notAsIn` a category. -}
  notAsIn :: Categorize token -> p
  default notAsIn
    :: (p ~ q token token, Choice q, Cochoice q)
    => Categorize token -> p
  notAsIn = satisfy . notAsIn

{- | A single token that satisfies a predicate. -}
satisfy
  :: (Tokenized a (p a a), Choice p, Cochoice p)
  => (a -> Bool) -> p a a
satisfy f = satisfied f >?< anyToken

{- | A specified stream of `tokens`. -}
tokens
  :: ( Foldable f, Tokenized a (p a a)
     , Monoidal p, Choice p
     , AsEmpty s, Cons s s a a
     )
  => f a -> p s s
tokens = foldr ((>:<) . token) asEmpty

-- instances
instance Categorized token => Tokenized token (token -> Bool) where
  anyToken _ = True
  token = (==)
  -- Tokens are collected into a `Set` once, & tested logarithmically.
  oneOf xs = (`Set.member` members) where members = Set.fromList (toList xs)
  notOneOf xs = (`Set.notMember` members)
    where members = Set.fromList (toList xs)
  asIn = lmap categorize . (==)
  notAsIn = lmap categorize . (/=)
instance Tokenized token (f token)
  => Tokenized token (Joker f token token) where
    anyToken = Joker (anyToken @token)
    token = Joker . token @token
    oneOf = Joker . oneOf @token
    notOneOf = Joker . notOneOf @token
    asIn = Joker . asIn @token
    notAsIn = Joker . notAsIn @token
instance Tokenized Char (ReadP Char) where
  anyToken = ReadP.get
  token = ReadP.char
  oneOf = ReadP.satisfy . oneOf
  notOneOf = ReadP.satisfy . notOneOf
  asIn = ReadP.satisfy . asIn
  notAsIn = ReadP.satisfy . notAsIn
instance Tokenized Char (ReadPrec Char) where
  anyToken = ReadPrec.lift anyToken
  token = ReadPrec.lift . token
  oneOf = ReadPrec.lift . oneOf
  notOneOf = ReadPrec.lift . notOneOf
  asIn = ReadPrec.lift . asIn
  notAsIn = ReadPrec.lift . notAsIn
deriving via (token -> Bool) instance Categorized token
  => Tokenized token (Predicate token)
instance (Categorized token, Arbitrary token) => Tokenized token (Gen token) where
  anyToken = arbitrary @token
  token = pure
  oneOf = Gen.elements . toList
  notOneOf xs = arbitrary `Gen.suchThat` (`notElem` xs)
  asIn cat = arbitrary `Gen.suchThat` ((==) cat . categorize)
  notAsIn cat = arbitrary `Gen.suchThat` ((/=) cat . categorize)
instance (RandomGen g, Monad m, Categorized token, Random token)
  => Tokenized token (StateT g m token) where
  anyToken = state random
  token = pure
  oneOf xs = do
    let ys = toList xs
    i <- state (randomR (0, length ys - 1))
    pure (ys !! i)
  notOneOf xs = iterateUntil (`notElem` xs) anyToken
  asIn cat = iterateUntil ((== cat) . categorize) anyToken
  notAsIn cat = iterateUntil ((/= cat) . categorize) anyToken

{- | A token examination, by the tokens it accepts, & the alternatives
of an algebra, whose fixed point is t'TokenClass'. Both t'TokenClass'es &
`Control.Lens.Grammar.RegEx.RegEx`pressions are algebras over it.
-}
data TokenExam token alg
  = OneOf (TokenSet token)
  | NotOneOf (TokenSet token) (CategoryTest token)
  {- | Two or more alternatives, none of them alternatives,
  in the order they're written.
  -}
  | Alternate alg alg [alg]

failExam :: Categorized token => TokenExam token alg
failExam = OneOf falseP

passExam :: Categorized token => TokenExam token alg
passExam = NotOneOf falseP (AndNotAsIn Set.empty)

isFailExam :: Categorized token => TokenExam token alg -> Bool
isFailExam (OneOf xs) = xs == falseP
isFailExam _ = False

isPassExam :: Categorized token => TokenExam token alg -> Bool
isPassExam (NotOneOf xs (AndNotAsIn ys)) = xs == falseP && Set.null ys
isPassExam _ = False

-- | The alternatives of an examination of t'TokenClass'es.
examAlternatives
  :: TokenExam token (TokenClass token) -> [TokenExam token (TokenClass token)]
examAlternatives = \case
  Alternate x y zs -> [exam | TokenClass exam <- x : y : zs]
  exam -> [exam]

{- | Alternatives, normalized: any which passes every token passes,
those which fail none are dropped, those of `OneOf` some tokens are one,
in place of the first, & each is kept once, in order, so that the
alternatives of alternatives are associative.
-}
alternatives
  :: Categorized token
  => [TokenExam token (TokenClass token)] -> TokenExam token (TokenClass token)
alternatives exams
  | any isPassExam exams = passExam
  | otherwise = case nub (unionOneOfs (filter (not . isFailExam) exams)) of
      [] -> failExam
      [exam] -> exam
      exam0 : exam1 : exams' ->
        Alternate (TokenClass exam0) (TokenClass exam1) (map TokenClass exams')
  where
    unionOneOfs xs = case [tokens' | OneOf tokens' <- xs] of
      [] -> xs
      tokenss -> placeFirst (OneOf (foldr (>|<) falseP tokenss)) xs
    placeFirst union = \case
      OneOf _ : rest -> union : [x | x <- rest, not (isOneOf x)]
      x : rest -> x : placeFirst union rest
      [] -> []
    isOneOf = \case
      OneOf _ -> True
      _ -> False

{- | `CategoryTest`s for `Categorized` tokens,
taken in conjunction with `NotOneOf` some `Set` of tokens.
-}
data CategoryTest token
  = AndAsIn (Categorize token)
  | AndNotAsIn (Set (Categorize token))

{- | t'TokenClass' forms a `Tokenized` `BooleanAlgebra`,
such that the following invariants hold.

> prop> trueP = anyToken
> prop> trueP = notOneOf []
> prop> falseP = oneOf []
> prop> notP . oneOf = notOneOf
> prop> notP . notOneOf = oneOf
> prop> notP . asIn = notAsIn
> prop> notP . notAsIn = asIn

t'TokenClass' is the fixed point algebra of t'TokenExam'.
t'TokenClass'es may be understood as normalizations of
`BooleanAlgebra` expressions generated by `Tokenized`
expressions.
-}
newtype TokenClass token = TokenClass (TokenExam token (TokenClass token))

-- | Fold a t'TokenClass' by an algebra of its t'TokenExam's.
foldTokenClass :: (TokenExam token a -> a) -> TokenClass token -> a
foldTokenClass alg (TokenClass exam) = alg (foldTokenClass alg <$> exam)

{- | `TokenAlgebra` extends `Tokenized` methods to support
`BooleanAlgebra` operations within a `tokenClass`.
When a `TokenAlgebra` is a `DisjunctiveMonoid`,
then `tokenClass` is expected to act homomorphically on disjunction.

> prop> falseP = tokenClass falseP
> prop> tokenClass x >|< tokenClass y = tokenClass (x >|< y)

Likewise, when a `TokenAlgebra` is `Control.Applicative.Alternative`,

> prop> empty = tokenClass falseP
> prop> tokenClass x <|> tokenClass y = tokenClass (x >|< y)

-}
class Tokenized token p => TokenAlgebra token p where
  tokenClass :: TokenClass token -> p
  default tokenClass
    :: (p ~ q token token, Alternator q, Cochoice q)
    => TokenClass token -> p
  -- Sets of tokens are tested by `Set.member`, logarithmically,
  -- rather than by `oneOf`'s & `notOneOf`'s `Foldable`, linearly.
  tokenClass = foldTokenClass $ \case
    OneOf chars -> satisfy (`tokenMember` chars)
    NotOneOf chars (AndAsIn cat) ->
      satisfy (notP (`tokenMember` chars) >&< asIn cat)
    NotOneOf chars (AndNotAsIn cats) ->
      satisfy (notP (`tokenMember` chars) >&< allP notAsIn cats)
    Alternate p q ps -> foldr1 (>|<) (p : q : ps)

deriving stock instance Generic (TokenExam token alg)
deriving stock instance Generic1 (TokenExam token)
deriving stock instance Generic (TokenClass token)
deriving stock instance Generic (CategoryTest token)
deriving stock instance
  (Categorized token, Read (TokenSet token), Read (Categorize token))
    => Read (TokenClass token)
deriving stock instance
  (Categorized token, Show (TokenSet token), Show (Categorize token))
    => Show (TokenClass token)
deriving newtype instance Categorized token => Eq (TokenClass token)
deriving newtype instance Categorized token => Ord (TokenClass token)
deriving newtype instance Categorized token => Tokenized token (TokenClass token)
deriving newtype instance Categorized token
  => DisjunctiveMonoid (TokenClass token)
deriving newtype instance Categorized token => BooleanAlgebra (TokenClass token)
instance Categorized token
  => TokenAlgebra token (TokenClass token) where
  tokenClass = id
instance Categorized token
  => TokenAlgebra token (TokenExam token (TokenClass token)) where
  tokenClass (TokenClass exam) = exam
instance Categorized token => TokenAlgebra token (token -> Bool) where
  tokenClass = foldTokenClass . flip $ \x -> \case
    OneOf xs -> tokenMember x xs
    NotOneOf xs (AndAsIn y) ->
      not (tokenMember x xs) && categorize x == y
    NotOneOf xs (AndNotAsIn ys) ->
      not (tokenMember x xs) && Set.notMember (categorize x) ys
    Alternate p q ps -> any ($ x) (p : q : ps)
instance TokenAlgebra token (f token)
  => TokenAlgebra token (Joker f token token) where
    tokenClass = Joker . tokenClass
instance TokenAlgebra Char (ReadP Char) where
  tokenClass = ReadP.satisfy . tokenClass
instance TokenAlgebra Char (ReadPrec Char) where
  tokenClass = ReadPrec.lift . tokenClass
deriving via (token -> Bool) instance Categorized token
  => TokenAlgebra token (Predicate token)
instance (Categorized token, Arbitrary token) => TokenAlgebra token (Gen token) where
  tokenClass = foldTokenClass $ \case
    OneOf xs -> oneOf (Exts.toList xs)
    NotOneOf xs (AndAsIn cat) -> arbitrary `Gen.suchThat`
      (\x -> not (tokenMember x xs) && categorize x == cat)
    NotOneOf xs (AndNotAsIn cats) -> arbitrary `Gen.suchThat`
      (\x -> not (tokenMember x xs) && categorize x `notElem` cats)
    Alternate p q ps -> Gen.oneof (p : q : ps)
instance (RandomGen g, Monad m, Categorized token, Random token)
  => TokenAlgebra token (StateT g m token) where
  tokenClass = foldTokenClass $ \case
    OneOf xs -> oneOf (Exts.toList xs)
    NotOneOf xs (AndAsIn cat) ->
      iterateUntil (\x -> not (tokenMember x xs) && categorize x == cat) anyToken
    NotOneOf xs (AndNotAsIn cats) ->
      iterateUntil (\x -> not (tokenMember x xs) && categorize x `notElem` cats) anyToken
    Alternate p q ps -> do
      i <- state (randomR (0, length ps + 1))
      (p : q : ps) !! i
instance Categorized token => Tokenized token (TokenExam token alg) where
  anyToken = passExam
  token a = OneOf (Exts.fromList [a])
  oneOf as | null as = failExam
  oneOf as = OneOf (Exts.fromList (toList as))
  notOneOf as | null as = passExam
  notOneOf as =
    NotOneOf (Exts.fromList (toList as)) (AndNotAsIn Set.empty)
  asIn cat = NotOneOf falseP (AndAsIn cat)
  notAsIn cat = NotOneOf falseP (AndNotAsIn (Set.singleton cat))
instance Categorized token
  => DisjunctiveMonoid (TokenExam token (TokenClass token)) where
  falseP = failExam
  x >|< y = alternatives (examAlternatives x <> examAlternatives y)
instance Categorized token
  => BooleanAlgebra (TokenExam token (TokenClass token)) where
  trueP = passExam
  notP exam | isFailExam exam = passExam
  notP exam | isPassExam exam = failExam
  notP (Alternate x y zs) =
    foldr1 (>&<) [notP exam | TokenClass exam <- x : y : zs]
  notP (OneOf xs) = notOneOf (Exts.toList xs)
  notP (NotOneOf xs (AndAsIn y)) = oneOf (Exts.toList xs) >|< notAsIn y
  notP (NotOneOf xs (AndNotAsIn ys)) = oneOf (Exts.toList xs) >|< anyP asIn ys
  x >&< y | x == y = x
  _ >&< exam | isFailExam exam = failExam
  exam >&< _ | isFailExam exam = failExam
  x >&< exam | isPassExam exam = x
  exam >&< z | isPassExam exam = z
  x >&< Alternate y z ws =
    foldr1 (>|<) [x >&< exam | TokenClass exam <- y : z : ws]
  Alternate x y ws >&< z =
    foldr1 (>|<) [exam >&< z | TokenClass exam <- x : y : ws]
  OneOf xs >&< OneOf ys = OneOf (tokenIntersection xs ys)
  OneOf xs >&< NotOneOf ys (AndAsIn z) = OneOf
    (filterTokens (\x -> categorize x == z) (tokenDifference xs ys))
  NotOneOf xs (AndAsIn y) >&< OneOf zs = OneOf
    (filterTokens (\z -> categorize z == y) (tokenDifference zs xs))
  OneOf xs >&< NotOneOf ys (AndNotAsIn zs) = OneOf
    (filterTokens (\x -> categorize x `notElem` zs) (tokenDifference xs ys))
  NotOneOf xs (AndNotAsIn ys) >&< OneOf zs = OneOf
    (filterTokens (\z -> categorize z `notElem` ys) (tokenDifference zs xs))
  NotOneOf xs (AndAsIn y) >&< NotOneOf ws (AndAsIn z) =
    if y /= z then failExam else NotOneOf
      (filterTokens (\x -> categorize x == y) (xs >|< ws)) (AndAsIn y)
  NotOneOf xs (AndAsIn y) >&< NotOneOf ws (AndNotAsIn zs) =
    if y `elem` zs then failExam else NotOneOf
      (filterTokens (\x -> categorize x == y) (xs >|< ws)) (AndAsIn y)
  NotOneOf xs (AndNotAsIn ys) >&< NotOneOf ws (AndAsIn z) =
    if z `elem` ys then failExam else NotOneOf
      (filterTokens (\x -> categorize x == z) (xs >|< ws)) (AndAsIn z)
  NotOneOf xs (AndNotAsIn ys) >&< NotOneOf ws (AndNotAsIn zs) =
    let
      xws = xs >|< ws
      yzs = Set.union ys zs
    in
      NotOneOf
        (filterTokens (\x -> categorize x `notElem` yzs) xws)
        (AndNotAsIn yzs)
deriving stock instance
  (Categorized token, Read (TokenSet token), Read alg, Read (Categorize token))
    => Read (TokenExam token alg)
deriving stock instance
  (Categorized token, Show (TokenSet token), Show alg, Show (Categorize token))
    => Show (TokenExam token alg)
deriving stock instance Functor (TokenExam token)
deriving stock instance Foldable (TokenExam token)
deriving stock instance Traversable (TokenExam token)
deriving stock instance (Categorized token, Eq alg) => Eq (TokenExam token alg)
deriving stock instance (Categorized token, Ord alg) => Ord (TokenExam token alg)
deriving stock instance Categorized token => Eq (CategoryTest token)
deriving stock instance Categorized token => Ord (CategoryTest token)
deriving stock instance
  (Categorized token, Read (TokenSet token), Read (Categorize token))
    => Read (CategoryTest token)
deriving stock instance
  (Categorized token, Show (TokenSet token), Show (Categorize token))
    => Show (CategoryTest token)

-- | The tokens of a set satisfying a predicate.
filterTokens :: Categorized token => (token -> Bool) -> TokenSet token -> TokenSet token
filterTokens p = Exts.fromList . filter p . Exts.toList
