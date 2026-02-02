{- |
Module      : Control.Lens.Grammar.Boole
Description : Boolean algebras & token classes
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable

Token classes form a Boolean algebra
-}

module Control.Lens.Grammar.Boole
  ( -- * token class
    TokenAlgebra (..)
  , TokenTest (..)
    -- * Boolean algebra
  , BooleanAlgebra (..)
  , andB, orB, allB, anyB
  ) where

import Control.Applicative
import Control.Lens.Grammar.Kleene
import Control.Lens.Grammar.Token
import Data.Foldable
import Data.Function (on)
import Data.Monoid
import Data.Profunctor
import Data.Profunctor.Distributor
import qualified Data.Set as Set
import GHC.Generics

class BooleanAlgebra b where

  (>&&<) :: b -> b -> b
  default (>&&<)
    :: (b ~ f bool, BooleanAlgebra bool, Applicative f) => b -> b -> b
  (>&&<) = liftA2 (>&&<)

  (>||<) :: b -> b -> b
  default (>||<)
    :: (b ~ f bool, BooleanAlgebra bool, Applicative f) => b -> b -> b
  (>||<) = liftA2 (>||<)

  notB :: b -> b
  default notB
    :: (b ~ f bool, BooleanAlgebra bool, Functor f) => b -> b
  notB = fmap notB

  fromBool :: Bool -> b
  default fromBool
    :: (b ~ f bool, BooleanAlgebra bool, Applicative f) => Bool -> b
  fromBool = pure . fromBool

andB :: (Foldable f, BooleanAlgebra b) => f b -> b
andB = foldl' (>&&<) (fromBool True)

orB :: (Foldable f, BooleanAlgebra b) => f b -> b
orB = foldl' (>||<) (fromBool False)

allB :: (Foldable f, BooleanAlgebra b) => (a -> b) -> f a -> b
allB f = foldl' (\b a -> b >&&< f a) (fromBool True)

anyB :: (Foldable f, BooleanAlgebra b) => (a -> b) -> f a -> b
anyB f = foldl' (\b a -> b >||< f a) (fromBool False)

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
instance BooleanAlgebra (x -> Bool)
instance Categorized token => TokenAlgebra token (token -> Bool) where
  tokenClass (TokenTest exam) = case exam of
    Fail -> const False
    Pass -> const True
    OneOf chars -> oneOf chars
    NotOneOf chars (AsIn cat) -> notOneOf chars >&&< asIn cat
    NotOneOf chars (NotAsIn cats) -> notOneOf chars >&&< allB notAsIn cats
    Alternate exam1 exam2 -> tokenClass exam1 >||< tokenClass exam2
instance (Applicative f, BooleanAlgebra bool)
  => BooleanAlgebra (Ap f bool)
deriving stock instance Generic (TokenTest token)
deriving stock instance
  (Categorized token, Read token, Read (Categorize token))
    => Read (TokenTest token)
deriving stock instance
  (Categorized token, Show token, Show (Categorize token))
    => Show (TokenTest token)
instance BooleanAlgebra Bool where
  fromBool = id
  notB = not
  (>&&<) = (&&)
  (>||<) = (||)
deriving newtype instance Categorized token
  => Eq (TokenTest token)
deriving newtype instance Categorized token
  => Ord (TokenTest token)
deriving newtype instance Categorized token
  => BooleanAlgebra (TokenTest token)
deriving newtype instance Categorized token
  => Tokenized token (TokenTest token)
instance Categorized token
  => TokenAlgebra token (RegEx token) where
  tokenClass (TokenTest tokenExam) = case tokenExam of
    Fail -> RegExam Fail
    Pass -> RegExam Pass
    OneOf as -> RegExam (OneOf as)
    NotOneOf as catTest -> RegExam (NotOneOf as catTest)
    Alternate exam1 exam2 ->
      RegExam (Alternate (tokenClass exam1) (tokenClass exam2))
instance Categorized token
  => BooleanAlgebra (RegExam token (TokenTest token)) where
  fromBool = \case
    False -> Fail
    True -> Pass
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
