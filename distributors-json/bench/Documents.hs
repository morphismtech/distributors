{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TemplateHaskell #-}

{- | Real-world documents, from @aeson@'s benchmarks (see @data/README.md@),
typed by records whose `Json` & @aeson@ instances are derived generically,
by the same `Options`.
-}
module Documents
  ( Search (..)
  , Story (..)
  , Metadata (..)
  , Geo (..)
  , Issue (..)
  , GitHubUser (..)
  , Label (..)
  , Milestone (..)
  , PullRequest (..)
  , Polygon (..)
  , Geometry (..)
  , Person (..)
  , Friend (..)
  , twitter10
  , twitter100
  , jp100
  , githubIssues
  , geoJson
  , people
  ) where

import Control.DeepSeq (NFData)
import Control.Lens.Grammar.Json
import Data.Aeson
import Data.ByteString (ByteString)
import Data.FileEmbed (embedFile)
import Data.Int (Int64)
import Data.Text (Text)
import GHC.Generics (Generic)

-- | Record fields named @id_@ & @type_@ are keyed @id@ & @type@.
keyed :: Options
keyed = defaultOptions
  { fieldLabelModifier = \case
      "id_" -> "id"
      "type_" -> "type"
      "default_" -> "default"
      field -> field
  }

-- Twitter --

data Search = Search
  { results :: [Story]
  , max_id :: Int64
  , since_id :: Int64
  , refresh_url :: Text
  , next_page :: Text
  , results_per_page :: Int
  , page :: Int
  , completed_in :: Double
  , since_id_str :: Text
  , max_id_str :: Text
  , query :: Text
  }
  deriving stock (Show, Generic)
  deriving anyclass (NFData, Json, ToJSON, FromJSON)

data Story = Story
  { from_user_id_str :: Text
  , profile_image_url :: Text
  , created_at :: Text
  , from_user :: Text
  , id_str :: Text
  , metadata :: Metadata
  , to_user_id :: Maybe Int64
  , text :: Text
  , id_ :: Int64
  , from_user_id :: Int64
  , geo :: Maybe Geo
  , iso_language_code :: Text
  , to_user_id_str :: Maybe Text
  , source :: Text
  , to_user :: Maybe Text
  }
  deriving stock (Show, Generic)
  deriving anyclass NFData
instance Json Story where json = jsonGeneric keyed
instance ToJSON Story where
  toJSON = genericToJSON keyed
  toEncoding = genericToEncoding keyed
instance FromJSON Story where parseJSON = genericParseJSON keyed

newtype Metadata = Metadata {result_type :: Text}
  deriving stock (Show, Generic)
  deriving anyclass (NFData, Json, ToJSON, FromJSON)

-- | A point, keyed literally @type_@ by Twitter.
data Geo = Geo {type_ :: Text, coordinates :: (Double, Double)}
  deriving stock (Show, Generic)
  deriving anyclass (NFData, Json, ToJSON, FromJSON)

-- GitHub --

data Issue = Issue
  { url :: Text
  , repository_url :: Text
  , labels_url :: Text
  , comments_url :: Text
  , events_url :: Text
  , html_url :: Text
  , id_ :: Int64
  , node_id :: Text
  , number :: Int
  , title :: Text
  , user :: GitHubUser
  , labels :: [Label]
  , state :: Text
  , locked :: Bool
  , assignee :: Maybe GitHubUser
  , assignees :: [GitHubUser]
  , milestone :: Maybe Milestone
  , comments :: Int
  , created_at :: Text
  , updated_at :: Text
  , closed_at :: Maybe Text
  , author_association :: Text
  , pull_request :: Maybe PullRequest
  , body :: Maybe Text
  }
  deriving stock (Show, Generic)
  deriving anyclass NFData

data GitHubUser = GitHubUser
  { login :: Text
  , id_ :: Int64
  , node_id :: Text
  , avatar_url :: Text
  , gravatar_id :: Text
  , url :: Text
  , html_url :: Text
  , followers_url :: Text
  , following_url :: Text
  , gists_url :: Text
  , starred_url :: Text
  , subscriptions_url :: Text
  , organizations_url :: Text
  , repos_url :: Text
  , events_url :: Text
  , received_events_url :: Text
  , type_ :: Text
  , site_admin :: Bool
  }
  deriving stock (Show, Generic)
  deriving anyclass NFData

data Label = Label
  { id_ :: Int64
  , node_id :: Text
  , url :: Text
  , name :: Text
  , color :: Text
  , default_ :: Bool
  , description :: Maybe Text
  }
  deriving stock (Show, Generic)
  deriving anyclass NFData

data Milestone = Milestone
  { url :: Text
  , html_url :: Text
  , labels_url :: Text
  , id_ :: Int64
  , node_id :: Text
  , number :: Int
  , title :: Text
  , description :: Maybe Text
  , creator :: GitHubUser
  , open_issues :: Int
  , closed_issues :: Int
  , state :: Text
  , created_at :: Text
  , updated_at :: Text
  , due_on :: Maybe Text
  , closed_at :: Maybe Text
  }
  deriving stock (Show, Generic)
  deriving anyclass NFData

data PullRequest = PullRequest
  { url :: Text
  , html_url :: Text
  , diff_url :: Text
  , patch_url :: Text
  }
  deriving stock (Show, Generic)
  deriving anyclass (NFData, Json, ToJSON, FromJSON)

instance Json Issue where json = jsonGeneric keyed
instance ToJSON Issue where
  toJSON = genericToJSON keyed
  toEncoding = genericToEncoding keyed
instance FromJSON Issue where parseJSON = genericParseJSON keyed
instance Json GitHubUser where json = jsonGeneric keyed
instance ToJSON GitHubUser where
  toJSON = genericToJSON keyed
  toEncoding = genericToEncoding keyed
instance FromJSON GitHubUser where parseJSON = genericParseJSON keyed
instance Json Label where json = jsonGeneric keyed
instance ToJSON Label where
  toJSON = genericToJSON keyed
  toEncoding = genericToEncoding keyed
instance FromJSON Label where parseJSON = genericParseJSON keyed
instance Json Milestone where json = jsonGeneric keyed
instance ToJSON Milestone where
  toJSON = genericToJSON keyed
  toEncoding = genericToEncoding keyed
instance FromJSON Milestone where parseJSON = genericParseJSON keyed

-- GeoJSON --

newtype Geometry = Geometry {geometry :: Polygon}
  deriving stock (Show, Generic)
  deriving anyclass (NFData, Json, ToJSON, FromJSON)

data Polygon = Polygon {type_ :: Text, coordinates :: [[[Double]]]}
  deriving stock (Show, Generic)
  deriving anyclass NFData
instance Json Polygon where json = jsonGeneric keyed
instance ToJSON Polygon where
  toJSON = genericToJSON keyed
  toEncoding = genericToEncoding keyed
instance FromJSON Polygon where parseJSON = genericParseJSON keyed

-- People --

data Person = Person
  { _id :: Text
  , index :: Int
  , guid :: Text
  , isActive :: Bool
  , balance :: Text
  , picture :: Text
  , age :: Int
  , eyeColor :: Text
  , name :: Text
  , gender :: Text
  , company :: Text
  , email :: Text
  , phone :: Text
  , address :: Text
  , about :: Text
  , registered :: Text
  , latitude :: Double
  , longitude :: Double
  , tags :: [Text]
  , friends :: [Friend]
  , greeting :: Text
  , favoriteFruit :: Text
  }
  deriving stock (Show, Generic)
  deriving anyclass (NFData, Json, ToJSON, FromJSON)

data Friend = Friend {id_ :: Int, name :: Text}
  deriving stock (Show, Generic)
  deriving anyclass NFData
instance Json Friend where json = jsonGeneric keyed
instance ToJSON Friend where
  toJSON = genericToJSON keyed
  toEncoding = genericToEncoding keyed
instance FromJSON Friend where parseJSON = genericParseJSON keyed

-- Documents --

-- | A document, decoded by @aeson@ once, failing loudly if it can't be.
document :: FromJSON a => String -> ByteString -> a
document file = either (error . (("benchmark data " <> file <> ": ") <>)) id
  . eitherDecodeStrict

twitter10 :: Search
twitter10 = document "twitter10" $(embedFile "bench/data/twitter10.json")

twitter100 :: Search
twitter100 = document "twitter100" $(embedFile "bench/data/twitter100.json")

jp100 :: Search
jp100 = document "jp100" $(embedFile "bench/data/jp100.json")

githubIssues :: [Issue]
githubIssues =
  document "github-issues" $(embedFile "bench/data/github-issues.json")

geoJson :: Geometry
geoJson = document "geometry" $(embedFile "bench/data/geometry.json")

people :: [Person]
people = document "buffer-builder" $(embedFile "bench/data/buffer-builder.json")
