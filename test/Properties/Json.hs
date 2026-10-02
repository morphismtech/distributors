{-# LANGUAGE OverloadedStrings #-}
module Properties.Json (jsonTypeSpec) where

import Control.Lens.Grammar (Bnf (startBnf))
import Control.Lens.Grammar.Json
import Data.Map (Map)
import Data.Scientific (Scientific)
import Data.Text (Text)
import Data.Vector (Vector)
import GHC.Generics (Generic)
import Test.Hspec

jsonTypeOf :: forall a. Json a => TsType
jsonTypeOf = startBnf (jsonType @a)

data Point = Point { px :: Scientific, py :: Scientific }
  deriving stock (Show, Generic)
instance Json Point

newtype Wrap = Wrap Scientific
  deriving stock (Show, Generic)
instance Json Wrap

data Pair = Pair Scientific Text
  deriving stock (Show, Generic)
instance Json Pair

data Unit = Unit
  deriving stock (Show, Generic)
instance Json Unit

data Color = Red | Green | Blue
  deriving stock (Show, Generic)
instance Json Color

data Shape
  = Circle Scientific
  | Square { side :: Scientific }
  deriving stock (Show, Generic)
instance Json Shape

data Profile = Profile
  { name :: Text
  , tags :: Vector Text
  , nickname :: Maybe Text
  } deriving stock (Show, Generic)
instance Json Profile

jsonTypeSpec :: Spec
jsonTypeSpec = describe "jsonType" $ do
  it "encodes basic types" $ do
    jsonTypeOf @Bool `shouldBe` TsBoolean
    jsonTypeOf @Text `shouldBe` TsString
    jsonTypeOf @Scientific `shouldBe` TsNumber
  it "encodes containers" $ do
    jsonTypeOf @(Vector Text) `shouldBe` TsArray TsString
    jsonTypeOf @(Maybe Text) `shouldBe` TsUnion TsString TsNull
    jsonTypeOf @(Map Text Scientific) `shouldBe` TsDict TsNumber
  it "encodes a record as an object" $
    jsonTypeOf @Point `shouldBe` TsObject [("px", TsNumber), ("py", TsNumber)]
  it "encodes a single-field constructor as its contents" $
    jsonTypeOf @Wrap `shouldBe` TsNumber
  it "encodes a positional multi-field constructor as a tuple" $
    jsonTypeOf @Pair `shouldBe` TsTuple [TsNumber, TsString]
  it "encodes a nullary single-constructor type as an empty tuple" $
    jsonTypeOf @Unit `shouldBe` TsTuple []
  it "encodes an all-nullary sum as a string" $
    jsonTypeOf @Color `shouldBe` TsString
  it "encodes a mixed sum as a tagged union of objects" $
    jsonTypeOf @Shape `shouldBe` TsUnion
      (TsObject [("tag", TsString), ("contents", TsNumber)])
      (TsObject [("tag", TsString), ("side", TsNumber)])
  it "encodes nested records" $
    jsonTypeOf @Profile `shouldBe` TsObject
      [ ("name", TsString)
      , ("tags", TsArray TsString)
      , ("nickname", TsUnion TsString TsNull)
      ]
