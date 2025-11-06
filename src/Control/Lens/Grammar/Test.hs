module Control.Lens.Grammar.Test
  ( BooleanAlgebra (..)
  , TestAlgebra (..)
  , TokenTest (..)
  , RegExam (..)
  , CategoryExam (..)
  ) where

import Control.Lens.Grammar.Token
import Data.Foldable (foldl')
import Data.Function (on)
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set

class BooleanAlgebra b where
  falseB, trueB :: b
  notB :: b -> b
  (>&&<), (>||<) :: b -> b -> b
  default falseB
    :: (b ~ f bool, BooleanAlgebra bool, Applicative f)
    => b
  default trueB
    :: (b ~ f bool, BooleanAlgebra bool, Applicative f)
    => b
  default notB
    :: (b ~ f bool, BooleanAlgebra bool, Functor f)
    => b -> b
  default (>||<)
    :: (b ~ f bool, BooleanAlgebra bool, Applicative f)
    => b -> b -> b
  default (>&&<)
    :: (b ~ f bool, BooleanAlgebra bool, Applicative f)
    => b -> b -> b
  trueB = pure trueB
  falseB = pure falseB
  notB = fmap notB
  (>&&<) = liftA2 (>&&<)
  (>||<) = liftA2 (>||<)

class BooleanAlgebra (Test alg) => TestAlgebra alg where
  type Test alg
  test :: Test alg -> alg

newtype TokenTest token = TokenTest (RegExam token (TokenTest token))

data RegExam token alg
  = Fail
  | Pass
  | OneOf (Set token)
  | NotOneOf (Set token) (CategoryExam token)
  | Alternate alg alg

data CategoryExam token
  = AsIn (Categorize token)
  | NotAsIn (Set (Categorize token))

--instances
instance BooleanAlgebra Bool where
  falseB = False
  trueB = True
  notB = not
  (>&&<) = (&&)
  (>||<) = (||)
instance BooleanAlgebra (x -> Bool)
instance (Applicative f, BooleanAlgebra bool)
  => BooleanAlgebra (Ap f bool)
deriving newtype instance
  (Categorized token, Ord token, Ord (Categorize token))
  => BooleanAlgebra (TokenTest token)
instance (Categorized token, Ord token, Ord (Categorize token))
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
    foldl'
    (Alternate `on` TokenTest)
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
    (Set.filter (\x -> notElem (categorize x) zs) (Set.difference xs ys))
  NotOneOf xs (NotAsIn ys) >&&< OneOf zs = OneOf
    (Set.filter (\z -> notElem (categorize z) ys) (Set.difference zs xs))
  NotOneOf xs (AsIn y) >&&< NotOneOf ws (AsIn z) =
    if y /= z then Fail else
      NotOneOf (Set.filter (\x -> categorize x == y) (Set.union xs ws)) (AsIn y)
  NotOneOf xs (AsIn y) >&&< NotOneOf ws (NotAsIn zs) =
    if elem y zs then Fail else
      NotOneOf (Set.filter (\x -> categorize x == y) (Set.union xs ws)) (AsIn y)
  NotOneOf xs (NotAsIn ys) >&&< NotOneOf ws (AsIn z) =
    if elem z ys then Fail else
      NotOneOf (Set.filter (\x -> categorize x == z) (Set.union xs ws)) (AsIn z)
  NotOneOf xs (NotAsIn ys) >&&< NotOneOf ws (NotAsIn zs) =
    NotOneOf (Set.filter (\x -> notElem (categorize x) yzs) xws) (NotAsIn yzs)
    where
      xws = Set.union xs ws
      yzs = Set.union ys zs

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

deriving stock instance Functor (RegExam token)
deriving stock instance Foldable (RegExam token)
deriving stock instance Traversable (RegExam token)
deriving stock instance (Categorized token, Eq alg) => Eq (RegExam token alg)
deriving stock instance
  (Categorized token, Ord token, Ord (Categorize token), Ord alg)
  => Ord (RegExam token alg)

deriving stock instance Categorized token => Eq (CategoryExam token)
deriving stock instance
  (Categorized token, Ord token, Ord (Categorize token))
  => Ord (CategoryExam token)

deriving newtype instance Categorized token => Eq (TokenTest token)
deriving newtype instance
  (Categorized token, Ord token, Ord (Categorize token))
  => Ord (TokenTest token)
