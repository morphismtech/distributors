{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Control.DeepSeq (NFData)
import Control.Lens.Grammar.Json
import Data.Aeson
  (FromJSON (..), ToJSON (..), Value (..), eitherDecode, encode, object, (.=))
import Data.Aeson.Encoding (encodingToLazyByteString)
import Data.Aeson.Types (parseEither)
import Data.ByteString.Lazy (ByteString)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as Text
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

ints :: [Int]
ints = [1 .. 10000]

texts :: [Text]
texts =
  [ Text.replicate 8 ("text \"" <> Text.pack (show i) <> "\" \\n ")
  | i <- [1 .. 1000 :: Int]
  ]

textMap :: Map Text Int
textMap = Map.fromList [("key" <> Text.pack (show i), i) | i <- [1 .. 1000]]

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
      , bench "aeson toJSON" (nf (encode . toJSON) a)
      , bench "Json jsonEncode"
          (nf (either (const "") encodingToLazyByteString . jsonEncode) a)
      , bench "Json jsonPrint" (nf (either (const "") encode . jsonPrint) a)
      ]
    , bgroup "toValue"
      [ bench "aeson toJSON" (nf toJSON a)
      , bench "Json jsonPrint" (nf (either (const Null) id . jsonPrint) a)
      ]
    , bgroup "fromValue"
      [ bench "aeson parseJSON" (nf (fromValueAeson a) val)
      , bench "Json jsonParse" (nf (fromValueJson a) val)
      ]
    , bgroup "decode"
      [ bench "aeson eitherDecode" (nf (decodeAeson a) bytes)
      , bench "Json jsonParse" (nf (decodeJson a) bytes)
      ]
    ]

fromValueAeson :: FromJSON a => a -> Value -> Maybe a
fromValueAeson _ = either (const Nothing) Just . parseEither parseJSON

fromValueJson :: Json a => a -> Value -> Maybe a
fromValueJson _ = either (const Nothing) Just . jsonParse

decodeAeson :: FromJSON a => a -> ByteString -> Maybe a
decodeAeson _ = either (const Nothing) Just . eitherDecode

decodeJson :: Json a => a -> ByteString -> Maybe a
decodeJson _ bytes = case eitherDecode bytes of
  Left _ -> Nothing
  Right val -> either (const Nothing) Just (jsonParse val)

main :: IO ()
main = defaultMain
  [ dataset "records" people
  , dataset "sums" shapes
  , dataset "ints" ints
  , dataset "texts" texts
  , dataset "map" textMap
  , dataset "value" value
  ]
