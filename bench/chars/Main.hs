{-# LANGUAGE DeriveAnyClass #-}
module Main (main) where

import Control.DeepSeq (NFData)
import Control.Lens.Grammar (ParsecState (..))
import Control.Lens.Grammar.Char.Redesign
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import GHC.Generics (Generic)
import Test.Tasty.Bench
import Text.Read (readMaybe)

data Person = Person
  { name :: String
  , age :: Int
  , email :: Maybe String
  , tags :: [String]
  , score :: Double
  } deriving stock (Eq, Show, Read, Generic)
    deriving anyclass (NFData, Textual)

data Shape = Circle Double | Rectangle Double Double | Point
  deriving stock (Eq, Show, Read, Generic)
  deriving anyclass (NFData, Textual)

data Weekday = Monday | Tuesday | Wednesday | Thursday | Friday
  deriving stock (Eq, Show, Read, Generic, Enum, Bounded)
  deriving anyclass (NFData, Textual)

data Rose = Rose Int [Rose]
  deriving stock (Eq, Show, Read, Generic)
  deriving anyclass (NFData, Textual)

people :: [Person]
people =
  [ Person
      { name = "person " <> show i
      , age = i `mod` 90
      , email = if even i then Just ("p" <> show i <> "@x.org") else Nothing
      , tags = ["a", "bb", "ccc"]
      , score = fromIntegral i / 7
      }
  | i <- [1 .. 1000 :: Int]
  ]

shapes :: [Shape]
shapes = take 3000 (cycle [Circle 1.5, Rectangle 2 (-3), Point])

weekdays :: [Weekday]
weekdays = take 10000 (cycle [minBound .. maxBound])

ints :: [Int]
ints = [i * (if even i then 1 else -1) | i <- [1 .. 10000]]

doubles :: [Double]
doubles = [fromIntegral i / 7 | i <- [1 .. 10000 :: Int]]

integers :: [Integer]
integers = [2 ^ (100 :: Int) + i | i <- [1 .. 2000]]

maybes :: [Maybe Int]
maybes = [if even i then Just i else Nothing | i <- [1 .. 10000]]

tuples :: [(Int, Char, Bool)]
tuples = [(i, toEnum (32 + i `mod` 90), even i) | i <- [1 .. 3000]]

strings :: [String]
strings = ["string \"" <> show i <> "\"\n" | i <- [1 .. 3000 :: Int]]

longString :: String
longString = concat (replicate 2000 "text with \"quotes\", \\ & \SOH\1234 ")

nested :: [[Int]]
nested = [[i .. i + 99] | i <- [1 .. 100]]

rose :: Rose
rose = grow (6 :: Int) 1
  where
    grow 0 i = Rose i []
    grow n i = Rose i [grow (n - 1) (i * 3 + j) | j <- [0 .. 2]]

intMap :: Map Int String
intMap = Map.fromList [(i, show i) | i <- [1 .. 1000]]

{- | Compare `Show` & `Read` with `Textual` on a dataset,
checking first that they agree on it.
-}
dataset
  :: (Textual a, Show a, Read a, Eq a, NFData a) => String -> a -> Benchmark
dataset label a = env agreed $ \str ->
  bgroup label
    [ bgroup "show"
      [ bench "Show show" (nf show a)
      , bench "Textual charShowsPrec" (nf charShow a)
      ]
    , bgroup "read"
      [ bench "Read read" (nf (readAs a) str)
      , bench "Textual charParsecPrec" (nf (charsReadAs a) str)
      , bench "Textual charReadsPrec" (nf (charReadsAs a) str)
      ]
    ]
  where
    agreed
      | charShow a /= show a = disagree "charShowsPrec"
      | charsReadAs a (show a) /= Just a = disagree "charParsecPrec"
      | charReadsAs a (show a) /= Just a = disagree "charReadsPrec"
      | otherwise = pure (show a)
    disagree run = fail (label <> ": " <> run <> " disagrees with Show & Read")

readAs :: Read a => a -> String -> Maybe a
readAs _ = readMaybe

charShow :: Textual a => a -> String
charShow a = charShowsPrec 0 a ""

charsReadAs :: Textual a => a -> String -> Maybe a
charsReadAs _ str = case charParsecPrec 0 str of
  ParsecState {parsecStream = "", parsecResult = Just a} -> Just a
  _ -> Nothing

charReadsAs :: Textual a => a -> String -> Maybe a
charReadsAs _ str = case [a | (a, "") <- charReadsPrec 0 str] of
  a : _ -> Just a
  [] -> Nothing

main :: IO ()
main = defaultMain
  [ dataset "records" people
  , dataset "sums" shapes
  , dataset "enums" weekdays
  , dataset "ints" ints
  , dataset "doubles" doubles
  , dataset "integers" integers
  , dataset "maybes" maybes
  , dataset "tuples" tuples
  , dataset "strings" strings
  , dataset "longString" longString
  , dataset "nested" nested
  , dataset "rose" rose
  , dataset "intMap" intMap
  ]
