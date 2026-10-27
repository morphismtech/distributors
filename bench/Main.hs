{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RequiredTypeArguments #-}
-- | Keep constant benchmarks, like `jsonTypes`, from being shared.
{-# OPTIONS_GHC -fno-full-laziness #-}
-- | A sum of records, like `Variant`, has partial fields.
{-# OPTIONS_GHC -Wno-partial-fields #-}
module Main (main) where

import Control.DeepSeq (NFData)
import Control.Lens.Grammar.Json
import Data.Aeson
  ( FromJSON (..), ToJSON (..), Value (..), decode, defaultOptions, encode
  , genericToEncoding, object, (.=)
  )
import Data.Aeson.Encoding (encodingToLazyByteString)
import Data.Aeson.Types (parseEither)
import Data.ByteString.Lazy (ByteString)
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HashMap
import Data.Int (Int8)
import Data.Maybe (isNothing)
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
    deriving anyclass (NFData, Json, FromJSON)

-- | @aeson@ encodes generic types directly, as it recommends.
instance ToJSON Person where toEncoding = genericToEncoding defaultOptions

data Shape = Circle Double | Rectangle Double Double | Point
  deriving stock (Show, Generic)
  deriving anyclass (NFData, Json, FromJSON)
instance ToJSON Shape where toEncoding = genericToEncoding defaultOptions

data Weekday = Monday | Tuesday | Wednesday | Thursday | Friday
  deriving stock (Show, Generic, Enum, Bounded)
  deriving anyclass (NFData, Json, FromJSON)
instance ToJSON Weekday where toEncoding = genericToEncoding defaultOptions

data Rose = Rose Int [Rose]
  deriving stock (Show, Generic)
  deriving anyclass (NFData, Json, FromJSON)
instance ToJSON Rose where toEncoding = genericToEncoding defaultOptions

-- | A wide record, of twenty fields.
data Wide = Wide
  { w01 :: Int, w02 :: Text, w03 :: Bool, w04 :: Double, w05 :: Maybe Int
  , w06 :: Int, w07 :: Text, w08 :: Bool, w09 :: Double, w10 :: Maybe Int
  , w11 :: Int, w12 :: Text, w13 :: Bool, w14 :: Double, w15 :: Maybe Int
  , w16 :: Int, w17 :: Text, w18 :: Bool, w19 :: Double, w20 :: Maybe Int
  } deriving stock (Show, Generic)
    deriving anyclass (NFData, Json, FromJSON)
instance ToJSON Wide where toEncoding = genericToEncoding defaultOptions

-- | A sum of records, tagged objects of their fields.
data Variant
  = Created {vid :: Int, vname :: Text}
  | Updated {vid :: Int, vchanges :: [Text]}
  | Deleted {vid :: Int}
  deriving stock (Show, Generic)
  deriving anyclass (NFData, Json, FromJSON)
instance ToJSON Variant where toEncoding = genericToEncoding defaultOptions

-- | Records nested deeply.
data Deep = Deep {title :: Text, child :: Maybe Deep}
  deriving stock (Show, Generic)
  deriving anyclass (NFData, Json, FromJSON)
instance ToJSON Deep where toEncoding = genericToEncoding defaultOptions

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

wides :: [Wide]
wides =
  [ Wide i t (even i) d m i t (odd i) d m i t (even i) d m i t (odd i) d m
  | i <- [1 .. 500 :: Int]
  , let
      t = "wide " <> Text.pack (show i)
      d = fromIntegral i / 3
      m = if even i then Just i else Nothing
  ]

variants :: [Variant]
variants = take 3000 $ cycle
  [Created 1 "created", Updated 2 ["a", "bb", "ccc"], Deleted 3]

deeps :: [Deep]
deeps = [chain (50 :: Int) i | i <- [1 .. 100 :: Int]]
  where
    chain 0 _ = Deep "leaf" Nothing
    chain n i = Deep (Text.pack (show (n, i))) (Just (chain (n - 1) i))

eithers :: [Either Int Text]
eithers =
  [if even i then Left i else Right (Text.pack (show i)) | i <- [1 .. 5000]]

longTexts :: [Text]
longTexts =
  [ Text.replicate 500 ("line \"" <> Text.pack (show i) <> "\"\t\\ ")
  | i <- [1 .. 10 :: Int]
  ]

hashMap :: HashMap Text Int
hashMap =
  HashMap.fromList [("key" <> Text.pack (show i), i) | i <- [1 .. 1000]]

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

{- | Compare @aeson@ & `Json` on a dataset,
checking first that they agree on it.
-}
dataset
  :: (Json a, ToJSON a, FromJSON a, NFData a) => String -> a -> Benchmark
dataset label a = env agreed $ \ ~(bytes, val) ->
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
  where
    agreed
      | jsonPrint a /= toJSON a = disagree "jsonPrint"
      | decode (encodingToLazyByteString (jsonEncode a)) /= Just (toJSON a) =
          disagree "jsonEncode"
      | isNothing (decodeJson a (encode a)) = disagree "jsonDecode"
      | otherwise = pure (encode a, toJSON a)
    disagree run = fail (label <> ": " <> run <> " disagrees with aeson")

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
  , dataset "wide" wides
  , dataset "variants" variants
  , dataset "deep" deeps
  , dataset "eithers" eithers
  , dataset "longTexts" longTexts
  , dataset "hashMap" hashMap
  , dataset "value" value
  , bgroup "typescript"
    [ bench "records" (nf (\() -> jsonTypes (type '[Person])) ())
    , bench "sums" (nf (\() -> jsonTypes [Shape]) ())
    , bench "rose" (nf (\() -> jsonTypes (type '[Rose])) ())
    , bench "value" (nf (\() -> jsonTypes [Value]) ())
    , bench "twice12" (nf (\() -> jsonTypes [Twice12]) ())
    ]
  ]
