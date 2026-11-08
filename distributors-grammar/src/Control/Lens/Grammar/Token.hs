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
import Data.Profunctor
import Data.Monoid.Disjunctive
import Data.Profunctor.Distributor
import Data.Profunctor.Monoidal
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Generics (Generic, Generic1)
import Data.Word
import Control.Monad.State (StateT, state)
import System.Random (RandomGen, Random, random, randomR)
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen (Gen)
import qualified Test.QuickCheck.Gen as Gen
import Text.ParserCombinators.ReadP (ReadP)
import qualified Text.ParserCombinators.ReadP as ReadP

{- | `Categorized` provides a type family `Categorize`
and a function to `categorize` tokens into disjoint categories.

>>> :kind! Categorize Char
Categorize Char :: *
= GeneralCategory

>>> categorize 'a'
LowercaseLetter
-}
class (Ord token, Ord (Categorize token), Enum (Categorize token))
  => Categorized token where
  type Categorize token
  type Categorize token = ()
  categorize :: token -> Categorize token
  default categorize :: Categorize token ~ () => token -> Categorize token
  categorize _ = ()
instance Categorized Char where
  type Categorize Char = GeneralCategory
  categorize = generalCategory
instance Categorized Word8
instance Categorized ()

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
  oneOf = flip elem
  notOneOf = flip notElem
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
  = OneOf (Set token)
  | NotOneOf (Set token) (CategoryTest token)
  | Alternate alg alg

failExam :: TokenExam token alg
failExam = OneOf Set.empty

passExam :: TokenExam token alg
passExam = NotOneOf Set.empty (AndNotAsIn Set.empty)

isFailExam :: TokenExam token alg -> Bool
isFailExam (OneOf xs) = Set.null xs
isFailExam _ = False

isPassExam :: TokenExam token alg -> Bool
isPassExam (NotOneOf xs (AndNotAsIn ys)) = Set.null xs && Set.null ys
isPassExam _ = False

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

t'TokenClass' is the fixed point algebra of t`TokenExam`.
t'TokenClass'es may be understood as normalizations of
`BooleanAlgebra` expressions generated by `Tokenized`
expressions.
-}
newtype TokenClass token = TokenClass (TokenExam token (TokenClass token))

-- | Fold a t'TokenClass' by an algebra of its t`TokenExam`s.
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
  tokenClass = foldTokenClass $ \case
    OneOf chars -> oneOf chars
    NotOneOf chars (AndAsIn cat) ->
      satisfy (notOneOf chars >&< asIn cat)
    NotOneOf chars (AndNotAsIn cats) ->
      satisfy (notOneOf chars >&< allP notAsIn cats)
    Alternate p q -> p >|< q

deriving stock instance Generic (TokenExam token alg)
deriving stock instance Generic1 (TokenExam token)
deriving stock instance Generic (TokenClass token)
deriving stock instance Generic (CategoryTest token)
deriving stock instance
  (Categorized token, Read token, Read (Categorize token))
    => Read (TokenClass token)
deriving stock instance
  (Categorized token, Show token, Show (Categorize token))
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
  tokenClass = foldTokenClass $ \case
    OneOf xs -> \x -> Set.member x xs
    NotOneOf xs (AndAsIn y) -> \x ->
      Set.notMember x xs && categorize x == y
    NotOneOf xs (AndNotAsIn ys) -> \x ->
      Set.notMember x xs && Set.notMember (categorize x) ys
    Alternate p q -> \x -> p x || q x
instance TokenAlgebra token (f token)
  => TokenAlgebra token (Joker f token token) where
    tokenClass = Joker . tokenClass
instance TokenAlgebra Char (ReadP Char) where
  tokenClass = ReadP.satisfy . tokenClass
instance (Categorized token, Arbitrary token) => TokenAlgebra token (Gen token) where
  tokenClass = foldTokenClass $ \case
    OneOf xs -> oneOf xs
    NotOneOf xs (AndAsIn cat) -> arbitrary `Gen.suchThat`
      (\x -> x `notElem` xs && categorize x == cat)
    NotOneOf xs (AndNotAsIn cats) -> arbitrary `Gen.suchThat`
      (\x -> x `notElem` xs && categorize x `notElem` cats)
    Alternate p q -> Gen.oneof [p, q]
instance (RandomGen g, Monad m, Categorized token, Random token)
  => TokenAlgebra token (StateT g m token) where
  tokenClass = foldTokenClass $ \case
    OneOf xs -> oneOf xs
    NotOneOf xs (AndAsIn cat) ->
      iterateUntil (\x -> x `notElem` xs && categorize x == cat) anyToken
    NotOneOf xs (AndNotAsIn cats) ->
      iterateUntil (\x -> x `notElem` xs && categorize x `notElem` cats) anyToken
    Alternate p q -> do
      b <- state random
      if (b :: Bool) then p else q
instance Categorized token => Tokenized token (TokenExam token alg) where
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
  => DisjunctiveMonoid (TokenExam token (TokenClass token)) where
  falseP = failExam
  x >|< y | x == y = x
  x >|< exam | isFailExam exam = x
  exam >|< y | isFailExam exam = y
  _ >|< exam | isPassExam exam = passExam
  exam >|< _ | isPassExam exam = passExam
  OneOf xs >|< OneOf ys = oneOf (Set.union xs ys)
  x >|< y = Alternate (TokenClass x) (TokenClass y)
instance Categorized token
  => BooleanAlgebra (TokenExam token (TokenClass token)) where
  trueP = passExam
  notP exam | isFailExam exam = passExam
  notP exam | isPassExam exam = failExam
  notP (Alternate (TokenClass x) (TokenClass y)) = notP x >&< notP y
  notP (OneOf xs) = notOneOf xs
  notP (NotOneOf xs (AndAsIn y)) = oneOf xs >|< notAsIn y
  notP (NotOneOf xs (AndNotAsIn ys)) = oneOf xs >|< anyP asIn ys
  x >&< y | x == y = x
  _ >&< exam | isFailExam exam = failExam
  exam >&< _ | isFailExam exam = failExam
  x >&< exam | isPassExam exam = x
  exam >&< z | isPassExam exam = z
  x >&< Alternate (TokenClass y) (TokenClass z) = (x >&< y) >|< (x >&< z)
  Alternate (TokenClass x) (TokenClass y) >&< z = (x >&< z) >|< (y >&< z)
  OneOf xs >&< OneOf ys = OneOf (Set.intersection xs ys)
  OneOf xs >&< NotOneOf ys (AndAsIn z) = OneOf
    (Set.filter (\x -> categorize x == z) (Set.difference xs ys))
  NotOneOf xs (AndAsIn y) >&< OneOf zs = OneOf
    (Set.filter (\z -> categorize z == y) (Set.difference zs xs))
  OneOf xs >&< NotOneOf ys (AndNotAsIn zs) = OneOf
    (Set.filter (\x -> categorize x `notElem` zs) (Set.difference xs ys))
  NotOneOf xs (AndNotAsIn ys) >&< OneOf zs = OneOf
    (Set.filter (\z -> categorize z `notElem` ys) (Set.difference zs xs))
  NotOneOf xs (AndAsIn y) >&< NotOneOf ws (AndAsIn z) =
    if y /= z then failExam else NotOneOf
      (Set.filter (\x -> categorize x == y) (Set.union xs ws)) (AndAsIn y)
  NotOneOf xs (AndAsIn y) >&< NotOneOf ws (AndNotAsIn zs) =
    if y `elem` zs then failExam else NotOneOf
      (Set.filter (\x -> categorize x == y) (Set.union xs ws)) (AndAsIn y)
  NotOneOf xs (AndNotAsIn ys) >&< NotOneOf ws (AndAsIn z) =
    if z `elem` ys then failExam else NotOneOf
      (Set.filter (\x -> categorize x == z) (Set.union xs ws)) (AndAsIn z)
  NotOneOf xs (AndNotAsIn ys) >&< NotOneOf ws (AndNotAsIn zs) =
    let
      xws = Set.union xs ws
      yzs = Set.union ys zs
    in
      NotOneOf
        (Set.filter (\x -> categorize x `notElem` yzs) xws)
        (AndNotAsIn yzs)
deriving stock instance
  (Categorized token, Read token, Read alg, Read (Categorize token))
    => Read (TokenExam token alg)
deriving stock instance
  (Categorized token, Show token, Show alg, Show (Categorize token))
    => Show (TokenExam token alg)
deriving stock instance Functor (TokenExam token)
deriving stock instance Foldable (TokenExam token)
deriving stock instance Traversable (TokenExam token)
deriving stock instance (Categorized token, Eq alg) => Eq (TokenExam token alg)
deriving stock instance (Categorized token, Ord alg) => Ord (TokenExam token alg)
deriving stock instance Categorized token => Eq (CategoryTest token)
deriving stock instance Categorized token => Ord (CategoryTest token)
deriving stock instance
  (Categorized token, Read token, Read (Categorize token))
    => Read (CategoryTest token)
deriving stock instance
  (Categorized token, Show token, Show (Categorize token))
    => Show (CategoryTest token)
