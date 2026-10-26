{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RequiredTypeArguments #-}
-- | Keep constant benchmarks, like `jsonTypes`, from being shared.
{-# OPTIONS_GHC -fno-full-laziness #-}
module Main (main) where

import Control.DeepSeq (NFData)
import Control.Lens.Grammar.Json
import Data.Aeson
  (FromJSON (..), ToJSON (..), Value (..), decode, encode, object, (.=))
import Data.Aeson.Encoding (encodingToLazyByteString)
import Data.Aeson.Types (parseEither)
import Data.ByteString.Lazy (ByteString)
import Data.Int (Int8)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Time (UTCTime)
import Data.Time.Clock.POSIX (posixSecondsToUTCTime)
import Data.Word (Word64)
import GHC.Generics (Generic)
import Test.Tasty.Bench

data Person = Person
  { name :: Text
  , age :: Int
  , email :: Maybe Text
  , tags :: [Text]
  , score :: Double
  } deriving stock (Show, Generic)
    deriving anyclass (NFData, Json, ToJSON, FromJSON)

data Shape = Circle Double | Rectangle Double Double | Point
  deriving stock (Show, Generic)
  deriving anyclass (NFData, Json, ToJSON, FromJSON)

data Weekday = Monday | Tuesday | Wednesday | Thursday | Friday
  deriving stock (Show, Generic, Enum, Bounded)
  deriving anyclass (NFData, Json, ToJSON, FromJSON)

data Rose = Rose Int [Rose]
  deriving stock (Show, Generic)
  deriving anyclass (NFData, Json, ToJSON, FromJSON)

-- | Twelve nested pairs, each its own type alias.
type Twice12 = Twice (Twice (Twice (Twice (Twice (Twice (Twice (Twice
  (Twice (Twice (Twice (Twice Double)))))))))))
data Twice a = Twice a a
  deriving stock Generic
  deriving anyclass Json

people :: [Person]
people =
  [ Person
      { name = "person " <> Text.pack (show i)
      , age = i `mod` 90
      , email = if even i then Just (Text.pack ("p" <> show i <> "@x.org"))
          else Nothing
      , tags = ["a", "bb", "ccc"]
      , score = fromIntegral i / 7
      }
  | i <- [1 .. 1000 :: Int]
  ]

shapes :: [Shape]
shapes = take 3000 (cycle [Circle 1.5, Rectangle 2 3, Point])

weekdays :: [Weekday]
weekdays = take 10000 (cycle [minBound .. maxBound])

ints :: [Int]
ints = [1 .. 10000]

doubles :: [Double]
doubles = [fromIntegral i / 7 | i <- [1 .. 10000 :: Int]]

integers :: [Integer]
integers = [2 ^ (100 :: Int) + i | i <- [1 .. 2000]]

word64s :: [Word64]
word64s = [maxBound - i | i <- [1 .. 10000]]

int8s :: [Int8]
int8s = take 10000 (cycle [minBound .. maxBound])

bools :: [Bool]
bools = take 10000 (cycle [True, False])

maybes :: [Maybe Int]
maybes = [if even i then Just i else Nothing | i <- [1 .. 10000]]

tuples :: [(Int, Text, Bool)]
tuples = [(i, Text.pack (show i), even i) | i <- [1 .. 3000]]

texts :: [Text]
texts =
  [ Text.replicate 8 ("text \"" <> Text.pack (show i) <> "\" \\n ")
  | i <- [1 .. 1000 :: Int]
  ]

strings :: [String]
strings = ["string " <> show i | i <- [1 .. 3000 :: Int]]

textMap :: Map Text Int
textMap = Map.fromList [("key" <> Text.pack (show i), i) | i <- [1 .. 1000]]

intMap :: Map Int Text
intMap = Map.fromList [(i, Text.pack (show i)) | i <- [1 .. 1000]]

pairMap :: Map (Int, Int) Bool
pairMap = Map.fromList [((i, i * 2), even i) | i <- [1 .. 1000]]

nested :: [[Int]]
nested = [[i .. i + 99] | i <- [1 .. 100]]

rose :: Rose
rose = grow (6 :: Int) 1
  where
    grow 0 i = Rose i []
    grow n i = Rose i [grow (n - 1) (i * 3 + j) | j <- [0 .. 2]]

times :: [UTCTime]
times =
  [posixSecondsToUTCTime (fromIntegral i * 1234.5) | i <- [1 .. 1000 :: Int]]

value :: Value
value = tree (6 :: Int)
  where
    tree 0 = Number 1
    tree n = object
      [ "leaf" .= String "abc"
      , "flag" .= Bool True
      , "children" .= [tree (n - 1), tree (n - 1), Null]
      ]

-- | Compare @aeson@ & `Json` on a dataset.
dataset
  :: (Json a, ToJSON a, FromJSON a, NFData a) => String -> a -> Benchmark
dataset label a = env (pure (encode a, toJSON a)) $ \ ~(bytes, val) ->
  bgroup label
    [ bgroup "encode"
      [ bench "aeson toEncoding" (nf encode a)
      , bench "Json jsonEncode" (nf (encodingToLazyByteString . jsonEncode) a)
      ]
    , bgroup "toValue"
      [ bench "aeson toJSON" (nf toJSON a)
      , bench "Json jsonPrint" (nf jsonPrint a)
      ]
    , bgroup "fromValue"
      [ bench "aeson parseJSON" (nf (fromValueAeson a) val)
      , bench "Json jsonParse" (nf (fromValueJson a) val)
      ]
    , bgroup "decode"
      [ bench "aeson decode" (nf (decodeAeson a) bytes)
      , bench "Json jsonDecode" (nf (decodeJson a) bytes)
      ]
    ]

fromValueAeson :: FromJSON a => a -> Value -> Maybe a
fromValueAeson _ = either (const Nothing) Just . parseEither parseJSON

fromValueJson :: Json a => a -> Value -> Maybe a
fromValueJson _ = either (const Nothing) Just . jsonParse

decodeAeson :: FromJSON a => a -> ByteString -> Maybe a
decodeAeson _ = decode

decodeJson :: Json a => a -> ByteString -> Maybe a
decodeJson _ = jsonDecode

main :: IO ()
main = defaultMain
  [ dataset "records" people
  , dataset "sums" shapes
  , dataset "enums" weekdays
  , dataset "ints" ints
  , dataset "doubles" doubles
  , dataset "integers" integers
  , dataset "word64s" word64s
  , dataset "int8s" int8s
  , dataset "bools" bools
  , dataset "maybes" maybes
  , dataset "tuples" tuples
  , dataset "texts" texts
  , dataset "strings" strings
  , dataset "textMap" textMap
  , dataset "intMap" intMap
  , dataset "pairMap" pairMap
  , dataset "nested" nested
  , dataset "rose" rose
  , dataset "times" times
  , dataset "value" value
  , bgroup "typescript"
    [ bench "records" (nf (\() -> jsonTypes (type '[Person])) ())
    , bench "sums" (nf (\() -> jsonTypes [Shape]) ())
    , bench "rose" (nf (\() -> jsonTypes (type '[Rose])) ())
    , bench "value" (nf (\() -> jsonTypes [Value]) ())
    , bench "twice12" (nf (\() -> jsonTypes [Twice12]) ())
    ]
  ]
