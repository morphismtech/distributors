-- | Test records of sums, for aeson's generic options, have partial fields.
{-# OPTIONS_GHC -Wno-partial-fields #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RequiredTypeArguments #-}
module Properties.Json
  ( jsonTypeSpec
  , aesonSpec
  , aesonCompat
  , aesonEncodeCompat
  , jsonErrorSpec
  , jsonObjectSpec
  , jsonOptionsSpec
  , jsonTupleSpec
  , jsonTupleChoiceSpec
  , jsonOptionalSpec
  , jsonCodecSpec
  , jsonPrintSpec
  ) where

import Control.Lens (coerced, non, only, prism')
import Control.Lens.Grammar
  ( dimap, lmap, manyP, optionP, optionalP, rule, someP
  , (>*<), (>+<), (>?), (>|<), (>~), (~<)
  )
import Control.Lens.Grammar.Json
import Data.Aeson
  ( FromJSON (..), Options (..), SumEncoding (..), ToJSON (..), Value (String)
  , camelTo2, decode, defaultOptions, genericToJSON
  , object, (.=)
  )
import Data.Aeson.Encoding (encodingToLazyByteString)
import Data.Aeson.Key (Key)
import Data.Aeson.KeyMap (KeyMap)
import Data.Aeson.Types
  ( DotNetTime (..), GToJSON', Zero, formatError, parseEither )
import Data.Char (toLower)
import Data.DList (DList)
import Data.DList qualified as DList
import Data.DList.DNonEmpty (DNonEmpty)
import Data.DList.DNonEmpty qualified as DNonEmpty
import Data.Either (isLeft, isRight)
import Data.Fix (Fix (..), Mu, Nu, unfoldMu, unfoldNu)
import Data.Fixed (E2, Fixed, Milli)
import Data.Functor.Compose (Compose)
import Data.Functor.Const (Const)
import Data.Functor.Identity (Identity)
import Data.Functor.Product qualified as Functor
import Data.Functor.Sum qualified as Functor
import Data.Functor.These (These1)
import Data.HashMap.Strict (HashMap)
import Data.HashSet (HashSet)
import Data.Int (Int8, Int16, Int32, Int64)
import Data.IntMap (IntMap)
import Data.IntSet (IntSet)
import Data.List.NonEmpty (NonEmpty)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Monoid qualified as Monoid
import Data.Ord (Down)
import Data.Primitive.Array (Array)
import Data.Primitive.PrimArray (PrimArray)
import Data.Primitive.SmallArray (SmallArray)
import Data.Proxy (Proxy (..))
import Data.Ratio (Ratio)
import Data.Scientific (Scientific)
import Data.Semigroup qualified as Semigroup
import Data.Sequence (Seq)
import Data.Set (Set)
import Data.Strict qualified as Strict
import Data.Tagged (Tagged)
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Lazy qualified as LText
import Data.Text.Short (ShortText)
import Data.These (These)
import Data.Time
  ( CalendarDiffDays, CalendarDiffTime, Day, DayOfWeek, DiffTime, LocalTime
  , NominalDiffTime, TimeOfDay, UTCTime, ZonedTime
  )
import Data.Time.Calendar.Month (Month)
import Data.Time.Calendar.Quarter (Quarter, QuarterOfYear)
import Data.Time.Clock.System (SystemTime)
import Data.Tree (Tree (..))
import Data.Tuple (Solo)
import Data.Typeable (Typeable, typeRep)
import Data.UUID.Types (UUID)
import Data.Vector (Vector)
import Data.Vector.Primitive qualified as VP
import Data.Vector.Storable qualified as VS
import Data.Vector.Unboxed qualified as VU
import Data.Version (Version, makeVersion)
import Data.Void (Void)
import Data.Word (Word8, Word16, Word32, Word64)
import Foreign.C.Types (CTime (..))
import GHC.Exts qualified as Exts
import GHC.Generics (Generic, Generically (..), Rep)
import Network.URI (URI, parseURI)
import Numeric.Natural (Natural)
import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Witherable qualified
import Test.QuickCheck hiding (Fixed)
import Test.QuickCheck.Instances ()

data Point = Point { px :: Scientific, py :: Scientific }
  deriving stock (Show, Generic)
  deriving anyclass (Json, ToJSON, FromJSON)

newtype Wrap = Wrap Scientific
  deriving stock (Show, Generic)
  deriving anyclass (Json, ToJSON, FromJSON)

data Pair = Pair Scientific Text
  deriving stock (Show, Generic)
  deriving anyclass (Json, ToJSON, FromJSON)

data Unit = Unit
  deriving stock (Show, Generic)
  deriving anyclass (Json, ToJSON, FromJSON)

data Color = Red | Green | Blue
  deriving stock (Show, Generic, Bounded, Enum)
  deriving anyclass (Json, ToJSON, FromJSON)

data Shape
  = Circle Scientific
  | Square { _side :: Scientific }
  deriving stock (Show, Generic)
  deriving anyclass (Json, ToJSON, FromJSON)

data Profile = Profile
  { name :: Text
  , tags :: Vector Text
  , nickname :: Maybe Text
  } deriving stock (Show, Generic)
    deriving anyclass (Json, ToJSON, FromJSON)

-- | @aeson@ instances derived via `Generically`,
-- mixing nullary & non-nullary constructors.
data Token = Word Text | Number Int | Pause
  deriving stock (Show, Generic)
  deriving anyclass Json
  deriving (ToJSON, FromJSON) via Generically Token

-- | Recursive.
data Peano = Zero | Succ Peano
  deriving stock (Show, Generic)
  deriving anyclass (Json, ToJSON, FromJSON)

-- | Mutually recursive.
newtype Forest = Forest [Branch]
  deriving stock (Show, Generic)
  deriving anyclass (Json, ToJSON, FromJSON)
data Branch = Branch Scientific Forest
  deriving stock (Show, Generic)
  deriving anyclass (Json, ToJSON, FromJSON)

-- | Parametric.
newtype Box a = Box a
  deriving stock (Show, Generic)
  deriving anyclass (ToJSON, FromJSON)
instance (Typeable a, Json a) => Json (Box a)

-- | An ill-formed object grammar, reading the same key twice.
newtype Dup = Dup (Int, Int)
  deriving stock Show
instance Json Dup where
  json = jsonTyped $ dimap (\(Dup p) -> p) Dup
    (jsonObject (("k" !: json) >*< ("k" !: json)))

-- | A limit, @10@ by default, which is missing exactly when it's @10@.
newtype Limit = Limit Int
  deriving stock (Eq, Show)
instance Json Limit where
  json = jsonTyped $ dimap (\(Limit n) -> n) Limit $
    jsonObject (non 10 ~< "limit" ?: json)

-- | An identifier and the rest of the properties, booleans.
newtype Extra = Extra (Int, [(Text, Bool)])
  deriving stock (Eq, Show)
instance Json Extra where
  json = jsonTyped $ dimap (\(Extra p) -> p) Extra $
    jsonObject ("id" !: json >*< jsonDict jsonText json)

-- | A count, positive, filtered from numbers.
newtype Counted = Counted Int
  deriving stock (Eq, Show)
instance Json Counted where
  json = jsonTyped $ dimap (\(Counted n) -> n) Counted $
    Witherable.mapMaybe (\n -> if n > 0 then Just n else Nothing) json

-- | A pet, by an object of a single field, named by its constructor.
data Pet = Cat Text | Dog Int
  deriving stock (Eq, Show)
instance Json Pet where
  json = jsonTyped $ dimap
    (\case Cat n -> Left n; Dog age -> Right age)
    (either Cat Dog)
    (jsonObject ("Cat" !: json >+< "Dog" !: json))

-- | An identifier and no other properties.
newtype Closed = Closed Int
  deriving stock (Eq, Show)
instance Json Closed where
  json = jsonTyped $ dimap (\(Closed n) -> n) Closed $
    jsonObjectStrict ("id" !: json)

jsonObjectSpec :: Spec
jsonObjectSpec = describe "jsonObject" $ do
  it "defaults a missing property" $ do
    jsonParse @Limit (object []) `shouldBe` Right (Limit 10)
    jsonPrintError (Limit 10) `shouldBe` Right (object [])
    jsonPrintError (Limit 3) `shouldBe` Right (object ["limit" .= (3 :: Int)])
  it "reads & writes the rest of an object" $ do
    let
      extra = Extra (1, [("a", True), ("b", False)])
      value =
        object ["id" .= (1 :: Int), "a" .= True, "b" .= False]
    jsonParse @Extra value `shouldBe` Right extra
    jsonPrintError extra `shouldBe` Right value
  it "doesn't print the rest over a named key" $
    printError (Extra (1, [("id", True)])) `shouldBe`
      Left "Error in $: cannot print key \"id\" twice"
  it "rejects keys which an object doesn't name" $ do
    jsonParse @Closed (object ["id" .= (1 :: Int)]) `shouldBe` Right (Closed 1)
    parseError @Closed (object ["id" .= (1 :: Int), "x" .= True])
      `shouldBe` "Error in $.x: unexpected true"
  it "chooses between alternative shapes" $ do
    jsonParse @Pet (object ["Cat" .= ("tom" :: Text)])
      `shouldBe` Right (Cat "tom")
    jsonParse @Pet (object ["Dog" .= (3 :: Int)]) `shouldBe` Right (Dog 3)
    jsonPrintError (Dog 3) `shouldBe` Right (object ["Dog" .= (3 :: Int)])
    declares (type Pet)
      [ "export type Int = number;"
      , "export type Pet = { Cat: string } | { Dog: Int };"
      ]
  it "types the rest of an object as an index signature" $ do
    declares (type Extra)
      [ "export type Extra = { id: Int; [key: string]: boolean | Int };"
      , "export type Int = number;"
      ]
    declares (type Closed)
      ["export type Closed = { id: Int };", "export type Int = number;"]
  it "doesn't print overlapping keys" $
    printError (Dup (1, 2)) `shouldBe`
      Left "Error in $: cannot print key \"k\" twice"
  it "doesn't parse a key twice" $
    parseError @Dup (object ["k" .= (1 :: Int)]) `shouldBe`
      "Error in $: expected another key \"k\", but found {\"k\":1}"
  it "doesn't type overlapping keys" $
    declares (type Dup)
      ["export type Dup = never;", "export type Int = number;"]
  it "ignores extra keys" $
    jsonParse @Point
      (object ["px" .= (1 :: Int), "py" .= (2 :: Int), "pz" .= (3 :: Int)])
      `shouldSatisfy` isRight

-- | A tuple of a number and rest strings, @[number, ...string[]]@.
newtype Rest = Rest (Scientific, [Text])
  deriving stock (Eq, Show)
instance Json Rest where
  json = jsonTyped $ dimap (\(Rest p) -> p) Rest $
    jsonTuple (jsonElem json >*< manyP (jsonElem json))

-- | Leading rest strings and a number, @[...string[], number]@.
newtype Leading = Leading ([Text], Scientific)
  deriving stock (Eq, Show)
instance Json Leading where
  json = jsonTyped $ dimap (\(Leading p) -> p) Leading $
    jsonTuple (manyP (jsonElem json) >*< jsonElem json)

-- | A number and an optional string, @[number, string?]@.
newtype Trailing = Trailing (Scientific, Maybe Text)
  deriving stock (Eq, Show)
instance Json Trailing where
  json = jsonTyped $ dimap (\(Trailing p) -> p) Trailing $
    jsonTuple (jsonElem json >*< optionalP (jsonElem json))

-- | An optional string before a number, @[string, number] | [number]@.
newtype Before = Before (Maybe Text, Scientific)
  deriving stock (Eq, Show)
instance Json Before where
  json = jsonTyped $ dimap (\(Before p) -> p) Before $
    jsonTuple (optionalP (jsonElem json) >*< jsonElem json)

-- | Two rests, @[...(number | string)[]]@.
newtype Rests = Rests ([Scientific], [Text])
  deriving stock (Eq, Show)
instance Json Rests where
  json = jsonTyped $ dimap (\(Rests p) -> p) Rests $
    jsonTuple (manyP (jsonElem json) >*< manyP (jsonElem json))

-- | Rest strings and an optional number,
-- @[...string[], number] | [...string[]]@.
newtype RestOptional = RestOptional ([Text], Maybe Scientific)
  deriving stock (Eq, Show)
instance Json RestOptional where
  json = jsonTyped $ dimap (\(RestOptional p) -> p) RestOptional $
    jsonTuple (manyP (jsonElem json) >*< optionalP (jsonElem json))

-- | Alternative elements, @[number | string]@.
newtype Alternative = Alternative (Either Scientific Text)
  deriving stock (Eq, Show)
instance Json Alternative where
  json = jsonTyped $ dimap (\(Alternative e) -> e) Alternative $
    jsonTuple (jsonElem json >+< jsonElem json)

-- | Alternative rests, @[...number[]] | [...string[]]@, not mixed.
newtype AlternativeRests = AlternativeRests (Either [Scientific] [Text])
  deriving stock (Eq, Show)
instance Json AlternativeRests where
  json = jsonTyped $ dimap (\(AlternativeRests e) -> e) AlternativeRests $
    jsonTuple (manyP (jsonElem json) >+< manyP (jsonElem json))

-- | A rest element in the middle, @[number, ...string[], boolean]@.
newtype Middle = Middle (Scientific, [Text], Bool)
  deriving stock (Eq, Show)
instance Json Middle where
  json = jsonTyped $ dimap
    (\(Middle (a, b, c)) -> (a, (b, c)))
    (\(a, (b, c)) -> Middle (a, b, c))
    (jsonTuple (jsonElem json >*< manyP (jsonElem json) >*< jsonElem json))

-- | At least one element, @[number, ...number[]]@.
newtype AtLeastOne = AtLeastOne [Scientific]
  deriving stock (Eq, Show)
instance Json AtLeastOne where
  json = jsonTyped $ dimap (\(AtLeastOne xs) -> xs) AtLeastOne
    (jsonTuple (someP (jsonElem json)))

-- | Alternative shapes, @[number, number?]@.
newtype Coord = Coord (Scientific, Scientific)
  deriving stock (Eq, Show)
instance Json Coord where
  json = jsonTyped $ dimap (\(Coord xy) -> xy) Coord $ jsonTuple $
    jsonElem json >*< jsonElem json >|< dimap fst (, 0) (jsonElem json)

-- | A defaulted element, @[number, number?]@.
newtype Defaulted = Defaulted (Scientific, Scientific)
  deriving stock (Eq, Show)
instance Json Defaulted where
  json = jsonTyped $ dimap (\(Defaulted xy) -> xy) Defaulted $ jsonTuple $
    jsonElem json >*< optionP (only 0) (jsonElem json)

jsonTupleChoiceSpec :: Spec
jsonTupleChoiceSpec = describe "jsonTuple choices" $ do
  it "has rest elements in the middle" $ do
    roundTrip (toJSON [toJSON (1 :: Int), "a", "b", toJSON True])
      (Middle (1, ["a", "b"], True))
    roundTrip (toJSON [toJSON (1 :: Int), toJSON False]) (Middle (1, [], False))
    declares (type Middle)
      ["export type Middle = [number, ...string[], boolean];"]
  it "has non-empty rest elements" $ do
    roundTrip (toJSON [1, 2 :: Int]) (AtLeastOne [1, 2])
    jsonParse @AtLeastOne (toJSON ([] :: [Int])) `shouldSatisfy` isLeft
    declares (type AtLeastOne)
      ["export type AtLeastOne = [number, ...number[]];"]
  it "has alternatives of the same type" $ do
    roundTrip (toJSON [1, 2 :: Int]) (Coord (1, 2))
    jsonParse @Coord (toJSON [1 :: Int]) `shouldBe` Right (Coord (1, 0))
    declares (type Coord) ["export type Coord = [number, number?];"]
  it "has defaulted elements" $ do
    roundTrip (toJSON [1 :: Int]) (Defaulted (1, 0))
    roundTrip (toJSON [1, 2 :: Int]) (Defaulted (1, 2))
    declares (type Defaulted) ["export type Defaulted = [number, number?];"]

-- | Round trip a `Value` through a `Json` grammar.
roundTrip :: forall a. (Json a, Eq a, Show a) => Value -> a -> Expectation
roundTrip value a = do
  jsonParse @a value `shouldBe` Right a
  jsonPrintError a `shouldBe` Right value

jsonTupleSpec :: Spec
jsonTupleSpec = describe "variadic jsonTuple" $ do
  it "has rest elements" $ do
    roundTrip (toJSON [toJSON (1 :: Int)]) (Rest (1, []))
    roundTrip (toJSON [toJSON (1 :: Int), "a", "b"]) (Rest (1, ["a", "b"]))
    declares (type Rest) ["export type Rest = [number, ...string[]];"]
  it "backtracks leading rest elements" $ do
    roundTrip (toJSON [toJSON (1 :: Int)]) (Leading ([], 1))
    roundTrip (toJSON ["a", "b", toJSON (1 :: Int)]) (Leading (["a", "b"], 1))
    declares (type Leading) ["export type Leading = [...string[], number];"]
  it "has optional elements" $ do
    roundTrip (toJSON [toJSON (1 :: Int)]) (Trailing (1, Nothing))
    roundTrip (toJSON [toJSON (1 :: Int), "a"]) (Trailing (1, Just "a"))
    declares (type Trailing) ["export type Trailing = [number, string?];"]
  it "expands optional elements before required elements" $ do
    roundTrip (toJSON [toJSON (1 :: Int)]) (Before (Nothing, 1))
    roundTrip (toJSON ["a", toJSON (1 :: Int)]) (Before (Just "a", 1))
    declares (type Before)
      ["export type Before = [string, number] | [number];"]
  it "merges rest elements" $ do
    roundTrip (toJSON [toJSON (1 :: Int), toJSON (2 :: Int), "a"])
      (Rests ([1, 2], ["a"]))
    declares (type Rests) ["export type Rests = [...(number | string)[]];"]
  it "expands optional elements after rest elements" $ do
    roundTrip (toJSON ["a", toJSON (1 :: Int)]) (RestOptional (["a"], Just 1))
    declares (type RestOptional)
      ["export type RestOptional = [...string[], number] | [...string[]];"]
  it "has alternative elements" $ do
    roundTrip (toJSON [toJSON (1 :: Int)]) (Alternative (Left 1))
    roundTrip (toJSON [String "a"]) (Alternative (Right "a"))
    declares (type Alternative)
      ["export type Alternative = [number | string];"]
  it "has alternative rest elements" $ do
    roundTrip (toJSON ["a", "b" :: Text]) (AlternativeRests (Right ["a", "b"]))
    jsonParse @AlternativeRests (toJSON [toJSON (1 :: Int), "a"])
      `shouldSatisfy` isLeft
    declares (type AlternativeRests)
      ["export type AlternativeRests = [...number[]] | [...string[]];"]
  it "locates failures in rest elements" $
    parseError @Rest (toJSON [toJSON (1 :: Int), "a", toJSON (2 :: Int)])
      `shouldBe` "Error in $[2]: expected string, but found 2"
  it "reports lengths" $
    parseError @Trailing (toJSON [toJSON (1 :: Int), "a", "b"]) `shouldBe`
      "Error in $: expected 2 elements or 1 element, \
      \but found [1,\"a\",\"b\"]"

-- | A partial grammar, which can't print `Uncovered`.
data Partial = Covered Scientific | Uncovered
  deriving stock (Eq, Show)
instance Json Partial where
  json = rule "Partial" $
    prism' Covered (\case Covered n -> Just n; _ -> Nothing) >? json

jsonPrintSpec :: Spec
jsonPrintSpec = describe "jsonPrintError" $ do
  it "labels failures with rules" $
    printError Uncovered `shouldBe` Left "Error in $: cannot print as Partial"
  it "locates failures" $ do
    printError [Covered 1, Uncovered] `shouldBe`
      Left "Error in $[1]: cannot print as Partial"
    printError (Rest (1, ["a"]), Uncovered) `shouldBe`
      Left "Error in $[1]: cannot print as Partial"
  it "reports overlapping keys" $
    printError (Dup (1, 2)) `shouldBe`
      Left "Error in $: cannot print key \"k\" twice"

-- | TypeScript type declarations, one per line.
declares :: forall a -> Json a => [Text] -> Expectation
declares a declarations = jsonTypes [a] `shouldBe` Text.unlines declarations

jsonTypeSpec :: Spec
jsonTypeSpec = describe "jsonTypes" $ do
  let point = "{ px: number; py: number }"
  it "declares nothing for types without rules" $ do
    declares Bool []
    declares Text []
    declares Scientific []
    declares (type String) []
    declares (Vector Text) []
    declares (Maybe Text) []
    declares (Map Text Scientific) []
  it "declares a record as an object" $
    declares (type Point) ["export type Point = " <> point <> ";"]
  it "declares a single-field constructor as its contents" $
    declares (type Wrap) ["export type Wrap = number;"]
  it "declares a positional multi-field constructor as a tuple" $
    declares (type Pair) ["export type Pair = [number, string];"]
  it "declares a nullary single-constructor type as an empty tuple" $
    declares (type Unit) ["export type Unit = [];"]
  it "declares an all-nullary sum as a union of string literals" $
    declares Color
      ["export type Color = \"Red\" | \"Green\" | \"Blue\";"]
  it "declares a mixed sum as a discriminated union of objects" $
    declares Shape
      [ "export type Shape = { tag: \"Circle\"; contents: number } \
        \| { tag: \"Square\"; _side: number };"
      ]
  it "declares nested records" $
    declares (type Profile)
      [ "export type Profile = \
        \{ name: string; tags: string[]; nickname?: null | string };"
      ]
  it "declares a recursive type" $
    declares Peano
      [ "export type Peano = { tag: \"Zero\" } \
        \| { tag: \"Succ\"; contents: Peano };"
      ]
  it "declares mutually recursive types" $ do
    let
      declarations =
        [ "export type Branch = [number, Forest];"
        , "export type Forest = Branch[];"
        ]
    declares (type Forest) declarations
    declares (type Branch) declarations
  it "declares each instantiation of a parametric type" $
    declares (type (Box (Box Scientific)))
      [ "export type Box_Box_Scientific = Box_Scientific;"
      , "export type Box_Scientific = number;"
      ]
  it "declares recursive non-generic types" $ do
    declares (Tree Scientific)
      ["export type Tree_Scientific = [number, Tree_Scientific[]];"]
    let
      declarations =
        [ "export type Fix_Either_Scientific = { Left: number } \
          \| { Right: Fix_Either_Scientific };"
        ]
    declares (type (Fix (Either Scientific))) declarations
    declares (Mu (Either Scientific)) declarations
    declares (Nu (Either Scientific)) declarations
    declares Value
      [ "export type Value = null | boolean | number | string \
        \| Value[] | { [key: string]: Value };"
      ]
  it "declares a non-empty list as a tuple with a rest element" $
    declares (type (Box (NonEmpty Text)))
      ["export type Box_NonEmpty_Text = [string, ...string[]];"]
  it "declares an enumeration as a union of string literals" $ do
    declares Ordering ["export type Ordering = \"LT\" | \"EQ\" | \"GT\";"]
    declares DayOfWeek
      [ "export type DayOfWeek = \"monday\" | \"tuesday\" | \"wednesday\" \
        \| \"thursday\" | \"friday\" | \"saturday\" | \"sunday\";"
      ]
    declares QuarterOfYear
      ["export type QuarterOfYear = \"q1\" | \"q2\" | \"q3\" | \"q4\";"]
  it "declares the rules of types without rules" $
    declares (type (Vector Point)) ["export type Point = " <> point <> ";"]
  it "declares each type once" $
    length (Text.lines (jsonTypes [Twice16])) `shouldBe` 16
  it "names colliding declarations uniquely" $
    declares (type Collide)
      [ "export type Collide = \
        \{ named: Point; typed: Properties_Json_Point };"
      , "export type Point = number;"
      , "export type Properties_Json_Point = " <> point <> ";"
      ]
  it "quotes property keys" $
    declares (type Optional)
      ["export type Optional = { a: number; \"b c\"?: string | number };"]
  it "declares types sharing their type aliases" $
    jsonTypes (type [Point, Box Point]) `shouldBe` Text.unlines
      [ "export type Box_Point = Point;"
      , "export type Point = " <> point <> ";"
      ]
  it "declares a rule of a rule as the rule" $
    declares (type Retyped) ["export type Retyped = number;"]
  it "declares unguarded recursion as its least fixpoint" $ do
    declares (type Chain) ["export type Chain = null;"]
    declares (type Loop) ["export type Loop = never;"]

-- | A rule of a rule, `jsonTyped` twice.
newtype Retyped = Retyped Scientific
  deriving stock Show
instance Json Retyped where
  json = jsonTyped (jsonTyped (dimap (\(Retyped n) -> n) Retyped json))

-- | Unguarded recursion, which only encodes as @null@.
newtype Chain = Chain (Maybe Chain)
  deriving stock (Show, Generic)
  deriving anyclass Json

-- | Unguarded recursion, which encodes nothing.
newtype Loop = Loop Loop
  deriving stock (Show, Generic)
  deriving anyclass Json

-- | Sixteen nested pairs, of exponentially many paths.
type Twice16 = Twice (Twice (Twice (Twice Twice12)))
type Twice12 = Twice (Twice (Twice (Twice (Twice (Twice (Twice (Twice
  (Twice (Twice (Twice (Twice Scientific)))))))))))
data Twice a = Twice a a
  deriving stock (Show, Generic)
instance (Typeable a, Json a) => Json (Twice a)

-- | A named rule and a type, both called @Point@.
data Collide = Collide {named :: Scientific, typed :: Point}
  deriving stock Show
instance Json Collide where
  json = jsonTyped $ jsonObject $ Collide
    <$> lmap named ("named" !: rule "Point" jsonNumber)
    <*> lmap typed ("typed" !: json)

-- | An optional property, with a key which isn't an identifier.
data Optional = Optional Scientific (Maybe (Either Text Scientific))
  deriving stock (Eq, Show)
instance Json Optional where
  json = jsonTyped $ jsonObject $ Optional
    <$> lmap (\(Optional a _) -> a) ("a" !: json)
    <*> lmap (\(Optional _ b) -> b)
      ("b c" ?: (jsonText >+< jsonNumber))

jsonOptionalSpec :: Spec
jsonOptionalSpec = describe "(?:)" $ do
  it "may be missing" $
    roundTrip (object ["a" .= (1 :: Int)]) (Optional 1 Nothing)
  it "may be present" $
    roundTrip (object ["a" .= (1 :: Int), "b c" .= ("x" :: Text)])
      (Optional 1 (Just (Left "x")))
  it "must be valid when present" $
    parseError @Optional (object ["a" .= (1 :: Int), "b c" .= True])
      `shouldBe` "Error in $['b c']: expected string or number, but found true"

-- | Encoding agrees with @aeson@.
jsonCodecSpec :: Spec
jsonCodecSpec = describe "jsonEncode" $ do
  it "derives aeson's instances from Json's" $ do
    let point = Point 1 2
    toJSON (ViaJson point) `shouldBe` jsonPrint point
    encodingToLazyByteString (toEncoding (ViaJson point))
      `shouldBe` encodingToLazyByteString (jsonEncode point)
    either Left (\(ViaJson p) -> Right (px p))
      (parseEither parseJSON (object ["px" .= True, "py" .= (2 :: Int)]))
      `shouldBe` Left "Error in $.px: expected number, but found true"
  codecCompat @Profile (Profile <$> arbitrary <*> arbitrary <*> arbitrary)
  codecCompat @(Map Text [Int]) arbitrary
  codecCompat @(Int, Maybe Bool, Text) arbitrary
  codecCompat @Value arbitrary
  codecCompat @Shape (oneof [Circle <$> arbitrary, Square <$> arbitrary])
  codecCompat @Color arbitraryBoundedEnum
  it "encodes in order" $
    encodingToLazyByteString <$> jsonEncodeError (Point 1 2)
      `shouldBe` Right "{\"px\":1,\"py\":2}"

codecCompat :: forall a. (Json a, ToJSON a, Show a, Typeable a) => Gen a -> Spec
codecCompat gen = it (show (typeRep (Proxy @a))) $ forAll gen $ \a ->
  (decode . encodingToLazyByteString <$> jsonEncodeError a)
    === Right (Just (toJSON a))

-- | The error message of parsing a `Value`.
parseError :: forall a. (Json a, Show a) => Value -> String
parseError = either errorText show . jsonParse @a

-- | The error message of printing a value.
printError :: Json a => a -> Either String Value
printError = either (Left . errorText) Right . jsonPrintError

errorText :: JsonError -> String
errorText err = formatError (jsonErrorPath err) (jsonErrorMessage err)

-- | The rules within which parsing a value failed.
parseRules :: forall a. Json a => Value -> [Tree String]
parseRules = either jsonErrorRules (const []) . jsonParse @a

-- | Alternative rules, which fail alike.
newtype Ambiguous = Ambiguous Scientific
instance Json Ambiguous where
  json = dimap (\(Ambiguous n) -> n) Ambiguous $
    rule "A" (jsonObject ("x" !: jsonNumber))
      >|< rule "B" (jsonObject ("x" !: jsonNumber))

jsonErrorSpec :: Spec
jsonErrorSpec = describe "jsonParse errors" $ do
  it "fails to decode text which isn't JSON, by aeson's message" $
    either errorText show (jsonDecode @Int "[1,")
      `shouldBe` "Error in $: Unexpected end-of-input, expecting JSON value"
  it "filters what's parsed" $ do
    jsonParse @Counted (toJSON (1 :: Int)) `shouldBe` Right (Counted 1)
    parseError @Counted (toJSON (-1 :: Int)) `shouldBe`
      "Error in $: expected Counted, but found -1"
  it "labels failures with rules" $ do
    parseError @Int (toJSON (1.5 :: Double)) `shouldBe`
      "Error in $: expected Int, but found 1.5"
    parseError @Natural (toJSON (-1 :: Int)) `shouldBe`
      "Error in $: expected Natural, but found -1"
    parseError @Char (String "ab") `shouldBe`
      "Error in $: expected Char, but found \"ab\""
    parseError @Color (String "Purple") `shouldBe`
      "Error in $: expected Color, but found \"Purple\""
  it "merges the expectations of alternatives" $ do
    parseError @(Maybe Int) (String "x") `shouldBe`
      "Error in $: expected null or Int, but found \"x\""
    parseError @(Either Int Text) (object ["Middle" .= (1 :: Int)]) `shouldBe`
      "Error in $: expected key \"Left\" or key \"Right\", \
      \but found {\"Middle\":1}"
    parseError @Shape (object ["tag" .= ("Triangle" :: Text)]) `shouldBe`
      "Error in $.tag: expected \"Circle\" or \"Square\", \
      \but found \"Triangle\""
  it "collects the rules which failures are within" $ do
    let
      badPoint = object ["px" .= ("a" :: Text), "py" .= (1 :: Int)]
    parseRules @Point badPoint `shouldBe` [Node "Point" []]
    parseRules @(Box Point) badPoint
      `shouldBe` [Node "Box Point" [Node "Point" []]]
    parseRules @[Point] (toJSON [badPoint]) `shouldBe` [Node "Point" []]
    parseRules @Point (object ["px" .= (1 :: Int)])
      `shouldBe` [Node "Point" []]
    parseRules @Point (toJSON (1 :: Int)) `shouldBe` []
    parseRules @Ambiguous (object ["x" .= ("s" :: Text)])
      `shouldBe` [Node "A" [], Node "B" []]
  it "prefers the failure of the alternative that applies" $
    parseError @Shape
      (object ["tag" .= ("Circle" :: Text), "contents" .= ("x" :: Text)])
      `shouldBe` "Error in $.contents: expected number, but found \"x\""
  it "locates failures" $ do
    parseError @Point (object ["px" .= (1 :: Int), "py" .= ("x" :: Text)])
      `shouldBe` "Error in $.py: expected number, but found \"x\""
    parseError @Point (object ["px" .= (1 :: Int)]) `shouldBe`
      "Error in $: expected key \"py\", but found {\"px\":1}"
    parseError @[Int] (toJSON [toJSON (1 :: Int), String "x"]) `shouldBe`
      "Error in $[1]: expected Int, but found \"x\""
    parseError @(Int, Text) (toJSON [1 :: Int]) `shouldBe`
      "Error in $: expected at least 2 elements, but found [1]"
    parseError @(Int, Text) (toJSON [toJSON (1 :: Int), toJSON (2 :: Int)])
      `shouldBe` "Error in $[1]: expected string, but found 2"

{- | Validate a `Json` instance against @aeson@'s instances:
printing agrees with `toJSON`, and parsing @aeson@'s encoding
agrees with `parseJSON`, comparing results by their encodings.
-}
aesonCompat
  :: forall a. (Json a, ToJSON a, FromJSON a, Show a, Typeable a)
  => Gen a -> Spec
aesonCompat gen = it (show (typeRep (Proxy @a))) $
  forAll gen $ \a ->
    let value = toJSON a
    in encodeCompat a
      .&&. parsed (jsonParse @a value)
        === parsed (parseEither (parseJSON @a) value)
  where
    parsed :: Either e a -> Maybe Value
    parsed = either (const Nothing) (Just . toJSON)

{- | Validate a `Json` instance against @aeson@'s `ToJSON` instance,
for types @aeson@ can encode but not decode:
printing agrees with `toJSON`, and parsing it reproduces the encoding.
-}
aesonEncodeCompat
  :: forall a. (Json a, ToJSON a, Show a, Typeable a)
  => Gen a -> Spec
aesonEncodeCompat gen = it (show (typeRep (Proxy @a))) $
  forAll gen encodeCompat

encodeCompat :: forall a. (Json a, ToJSON a) => a -> Property
encodeCompat a =
  let value = toJSON a
  in jsonPrintError a === Right value
    .&&. fmap toJSON (jsonParse @a value) === Right value

aesonSpec :: Spec
aesonSpec = describe "Json agrees with aeson" $ do
  -- base
  aesonCompat @Bool arbitrary
  aesonCompat @Ordering arbitrary
  aesonCompat @() arbitrary
  aesonCompat @Char arbitrary
  aesonCompat @String arbitrary
  aesonCompat @[Int] arbitrary
  aesonCompat @(Maybe Int) arbitrary
  aesonCompat @(Maybe (Maybe Bool)) arbitrary
  aesonCompat @(Either Int Text) arbitrary
  aesonCompat @Double arbitrary
  aesonCompat @Double (elements [0/0, 1/0, negate 1/0])
  aesonCompat @Float arbitrary
  aesonCompat @(Ratio Integer) arbitrary
  aesonCompat @Milli arbitrary
  aesonCompat @Int arbitrary
  aesonCompat @Int8 arbitrary
  aesonCompat @Int16 arbitrary
  aesonCompat @Int32 arbitrary
  aesonCompat @Int64 arbitrary
  aesonCompat @Word arbitrary
  aesonCompat @Word8 arbitrary
  aesonCompat @Word16 arbitrary
  aesonCompat @Word32 arbitrary
  aesonCompat @Word64 arbitrary
  aesonCompat @Integer arbitrary
  aesonCompat @Natural arbitrary
  aesonCompat @CTime (CTime <$> arbitrary)
  aesonCompat @Version genVersion
  aesonCompat @(NonEmpty Int) arbitrary
  aesonCompat @(Solo Int) arbitrary
  aesonCompat @(Identity Int) arbitrary
  aesonCompat @[Identity Char] arbitrary
  aesonCompat @(Const Int Bool) arbitrary
  aesonCompat @(Compose Maybe [] Int) arbitrary
  aesonCompat @(Functor.Product Maybe [] Int) arbitrary
  aesonCompat @(Functor.Sum Maybe [] Int) arbitrary
  aesonCompat @(Down Int) arbitrary
  aesonCompat @[Down Char] arbitrary
  aesonCompat @(Monoid.Dual Int) arbitrary
  aesonCompat @(Monoid.First Int) arbitrary
  aesonCompat @(Monoid.Last Int) arbitrary
  aesonCompat @(Semigroup.Min Int) arbitrary
  aesonCompat @(Semigroup.Max Int) arbitrary
  aesonCompat @(Semigroup.First Int) arbitrary
  aesonCompat @(Semigroup.Last Int) arbitrary
  aesonCompat @(Semigroup.WrappedMonoid [Int]) arbitrary
  aesonCompat @(Semigroup.Sum Int) arbitrary
  aesonCompat @(Semigroup.Product Int) arbitrary
  aesonCompat @Semigroup.All arbitrary
  aesonCompat @Semigroup.Any arbitrary
  aesonCompat @(Proxy Int) (pure Proxy)
  it "Void never parses" $
    jsonParse @Void (toJSON ()) `shouldSatisfy` isLeft
  -- generics
  aesonCompat @Point (Point <$> arbitrary <*> arbitrary)
  aesonCompat @Wrap (Wrap <$> arbitrary)
  aesonCompat @Pair (Pair <$> arbitrary <*> arbitrary)
  aesonCompat @Unit (pure Unit)
  aesonCompat @Color arbitraryBoundedEnum
  aesonCompat @Shape (oneof [Circle <$> arbitrary, Square <$> arbitrary])
  aesonCompat @Profile (Profile <$> arbitrary <*> arbitrary <*> arbitrary)
  aesonCompat @Token
    (oneof [Word <$> arbitrary, Number <$> arbitrary, pure Pause])
  aesonCompat @Peano genPeano
  aesonCompat @Forest genForest
  aesonCompat @(Box (Box Int)) (Box . Box <$> arbitrary)
  -- tuples
  aesonCompat @(Int, Text) arbitrary
  aesonCompat @(Int, Text, Bool) arbitrary
  aesonCompat @(Int, Text, Bool, Char) arbitrary
  aesonCompat @(Int, Text, Bool, Char, Int) arbitrary
  aesonCompat @(Int, Text, Bool, Char, Int, Text) arbitrary
  aesonCompat @(Int, Text, Bool, Char, Int, Text, Bool) arbitrary
  aesonCompat @(Int, Text, Bool, Char, Int, Text, Bool, Char) arbitrary
  aesonCompat @(Int, Text, Bool, Char, Int, Text, Bool, Char, Int) arbitrary
  aesonCompat @(Int, Text, Bool, Char, Int, Text, Bool, Char, Int, Text)
    arbitrary
  aesonCompat @(Int, Text, Bool, Char, Int, Text, Bool, Char, Int, Text, Bool)
    ((,,,,,,,,,,) <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
      <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
      <*> arbitrary <*> arbitrary)
  aesonCompat
    @(Int, Text, Bool, Char, Int, Text, Bool, Char, Int, Text, Bool, Char)
    ((,,,,,,,,,,,) <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
      <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
      <*> arbitrary <*> arbitrary <*> arbitrary)
  aesonCompat
    @(Int, Text, Bool, Char, Int, Text, Bool, Char, Int, Text, Bool, Char, Int)
    ((,,,,,,,,,,,,) <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
      <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
      <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary)
  aesonCompat
    @( Int, Text, Bool, Char, Int, Text, Bool, Char, Int, Text, Bool, Char
     , Int, Text )
    ((,,,,,,,,,,,,,) <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
      <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
      <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary)
  aesonCompat
    @( Int, Text, Bool, Char, Int, Text, Bool, Char, Int, Text, Bool, Char
     , Int, Text, Bool )
    ((,,,,,,,,,,,,,,) <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
      <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
      <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
      <*> arbitrary)
  -- text & scientific
  aesonCompat @Text arbitrary
  aesonCompat @LText.Text arbitrary
  aesonCompat @ShortText arbitrary
  aesonCompat @Scientific arbitrary
  -- containers
  aesonCompat @(Seq Int) arbitrary
  aesonCompat @(Set Int) arbitrary
  aesonCompat @IntSet arbitrary
  aesonCompat @(IntMap Text) arbitrary
  aesonCompat @(Tree Int) arbitrary
  -- maps
  aesonCompat @(Map [Int] Int) arbitrary
  aesonCompat @(Map (Int, Bool) Text) arbitrary
  aesonCompat @(Map (Int, Bool, Char) Text) arbitrary
  aesonCompat @(Map (Int, Bool, Char, Text) Text) arbitrary
  aesonCompat @(Map Text Int) arbitrary
  aesonCompat @(Map String Int) arbitrary
  aesonCompat @(Map Bool Int) arbitrary
  aesonCompat @(Map Char Int) arbitrary
  aesonCompat @(Map Int Bool) arbitrary
  aesonCompat @(Map Int8 Bool) arbitrary
  aesonCompat @(Map Word64 Bool) arbitrary
  aesonCompat @(Map Integer Bool) arbitrary
  aesonCompat @(Map Natural Bool) arbitrary
  aesonCompat @(Map Double Bool) arbitrary
  -- neither @aeson@ nor `Json` round trip @-0.0@ keys, through `Scientific`
  aesonCompat @(Map Double Bool) (Map.fromList . map (, True) <$>
    sublistOf [0/0, 1/0, negate 1/0, 0])
  aesonCompat @(Map Float Bool) arbitrary
  aesonEncodeCompat @(Map (Fixed E2) Bool) arbitrary
  aesonEncodeCompat @(Map Scientific Bool) arbitrary
  aesonCompat @(Map LText.Text Bool) arbitrary
  aesonCompat @(Map ShortText Bool) arbitrary
  aesonCompat @(Map Version Bool)
    (Map.fromList <$> listOf ((,) <$> genVersion <*> arbitrary))
  aesonCompat @(Map (Solo Int) Bool) arbitrary
  aesonCompat @(Map (Identity Text) Bool) arbitrary
  aesonCompat @(Map [Identity Char] Bool) arbitrary
  aesonCompat @(Map (Const Int Bool) Bool) arbitrary
  aesonCompat @(Map (Tagged Bool Int) Bool) arbitrary
  aesonCompat @(Map UUID Bool) arbitrary
  aesonCompat @(Map Key Bool) arbitrary
  aesonCompat @(Map Day Bool) arbitrary
  aesonCompat @(Map Month Bool) arbitrary
  aesonCompat @(Map Quarter Bool) arbitrary
  aesonCompat @(Map TimeOfDay Bool) arbitrary
  aesonCompat @(Map LocalTime Bool) arbitrary
  aesonCompat @(Map UTCTime Bool) arbitrary
  aesonCompat @(Map DayOfWeek Bool) arbitrary
  aesonCompat @(Map QuarterOfYear Bool) arbitrary
  aesonCompat @(Map URI Bool)
    (Map.fromList <$> listOf ((,) <$> genURI <*> arbitrary))
  aesonCompat @(HashMap Text Int) arbitrary
  -- dlist
  aesonCompat @(DList Int) (DList.fromList <$> arbitrary)
  aesonCompat @(DNonEmpty Int) (DNonEmpty.fromNonEmpty <$> arbitrary)
  -- vector
  aesonCompat @(Vector Int) arbitrary
  aesonCompat @(VS.Vector Int) arbitrary
  aesonCompat @(VP.Vector Int) (VP.fromList <$> arbitrary)
  aesonCompat @(VU.Vector Int) arbitrary
  -- primitive
  aesonCompat @(Array Char) (Exts.fromList <$> arbitrary)
  aesonCompat @(SmallArray Int) (Exts.fromList <$> arbitrary)
  aesonCompat @(PrimArray Int) (Exts.fromList <$> arbitrary)
  -- unordered-containers
  aesonCompat @(HashSet Int) arbitrary
  aesonCompat @(HashMap (Int, Int) Bool) arbitrary
  -- aeson
  aesonCompat @Key arbitrary
  aesonCompat @(KeyMap Int) arbitrary
  aesonCompat @Value arbitrary
  aesonCompat @DotNetTime (DotNetTime <$> arbitrary)
  -- time
  aesonCompat @Day arbitrary
  aesonCompat @Month arbitrary
  aesonCompat @Quarter arbitrary
  aesonCompat @TimeOfDay arbitrary
  aesonCompat @LocalTime arbitrary
  aesonCompat @ZonedTime arbitrary
  aesonCompat @UTCTime arbitrary
  aesonCompat @NominalDiffTime arbitrary
  aesonCompat @DiffTime arbitrary
  aesonCompat @SystemTime arbitrary
  aesonCompat @CalendarDiffTime arbitrary
  aesonCompat @CalendarDiffDays arbitrary
  aesonCompat @DayOfWeek arbitrary
  aesonCompat @QuarterOfYear arbitrary
  -- uuid-types & network-uri
  aesonCompat @UUID arbitrary
  aesonCompat @URI genURI
  -- data-fix
  aesonCompat @(Fix (Either Int)) genFix
  aesonCompat @(Mu (Either Int)) (unfoldMu unFix <$> genFix)
  aesonCompat @(Nu (Either Int)) (unfoldNu unFix <$> genFix)
  -- tagged & these & strict
  aesonCompat @(Tagged Bool Int) arbitrary
  aesonCompat @(These Int Text) arbitrary
  aesonCompat @(These1 Maybe [] Int) arbitrary
  aesonCompat @(Strict.Maybe Int) arbitrary
  aesonCompat @(Strict.Either Int Text) arbitrary
  aesonCompat @(Strict.These Int Text) arbitrary
  aesonCompat @(Strict.Pair Int Text) arbitrary

genVersion :: Gen Version
genVersion = makeVersion <$> listOf1 (chooseInt (0, 100))

genURI :: Gen URI
genURI = elements
  [ uri
  | Just uri <- parseURI <$>
    [ "https://example.com/a/b?c=d#e"
    , "mailto:someone@example.com"
    , "file:///tmp/x.txt"
    , "urn:isbn:0451450523"
    ]
  ]

genPeano :: Gen Peano
genPeano = sized $ \n -> if n <= 0 then pure Zero
  else frequency [(1, pure Zero), (3, Succ <$> resize (n - 1) genPeano)]

genForest :: Gen Forest
genForest = sized $ \n -> Forest <$> if n <= 0 then pure []
  else listOf (Branch <$> arbitrary <*> resize (n `div` 3) genForest)

genFix :: Gen (Fix (Either Int))
genFix = sized $ \n -> if n <= 0
  then Fix . Left <$> arbitrary
  else frequency
    [ (1, Fix . Left <$> arbitrary)
    , (3, Fix . Right <$> resize (n `div` 2) genFix)
    ]

-- | Constructors of each kind, for @aeson@'s generic options,
-- whose records' fields are partial.
data Sample
  = Nullary
  | Unary Int
  | Binary Int Text
  | Record {recordInt :: Int, recordMaybe :: Maybe Text}
  | Single {single :: Bool}
  deriving stock (Eq, Show, Generic)
instance Arbitrary Sample where
  arbitrary = oneof
    [ pure Nullary, Unary <$> arbitrary, Binary <$> arbitrary <*> arbitrary
    , Record <$> arbitrary <*> arbitrary, Single <$> arbitrary
    ]

-- | A single constructor of a single field.
data Lone = Lone {lone :: Int}
  deriving stock (Eq, Show, Generic)
instance Arbitrary Lone where arbitrary = Lone <$> arbitrary

-- | An enumeration.
data Hue = Cyan | Magenta | Yellow
  deriving stock (Eq, Show, Generic, Enum, Bounded)
instance Arbitrary Hue where arbitrary = arbitraryBoundedEnum

-- | Options, by a type.
class Optioned o where options :: Options
data Defaults
instance Optioned Defaults where options = defaultOptions
data Untagged
instance Optioned Untagged where
  options = defaultOptions {sumEncoding = UntaggedValue}
data SingleField
instance Optioned SingleField where
  options = defaultOptions {sumEncoding = ObjectWithSingleField}
data TwoElements
instance Optioned TwoElements where
  options = defaultOptions {sumEncoding = TwoElemArray}
data Tweaked
instance Optioned Tweaked where
  options = defaultOptions
    { fieldLabelModifier = camelTo2 '_'
    , constructorTagModifier = map toLower
    , sumEncoding = TaggedObject "kind" "value"
    , allNullaryToStringTag = False
    , omitNothingFields = True
    , unwrapUnaryRecords = True
    , tagSingleConstructors = True
    }

-- | A value, by `jsonGeneric` of options.
newtype By o a = By a
  deriving stock (Eq, Show)
instance Optioned o => Json (By o Sample) where
  json = coerced >~ jsonGeneric @Sample (options @o)
instance Optioned o => Json (By o Lone) where
  json = coerced >~ jsonGeneric @Lone (options @o)
instance Optioned o => Json (By o Hue) where
  json = coerced >~ jsonGeneric @Hue (options @o)

-- | `jsonGeneric` agrees with @aeson@'s generic instances by options.
agreesByOptions
  :: forall o a
   . ( Optioned o, Json (By o a), Arbitrary a, Eq a, Show a, Generic a
     , GToJSON' Value Zero (Rep a) )
  => String -> Spec
agreesByOptions title = describe title $ do
  prop "prints as aeson" $ \(a :: a) ->
    jsonPrint (By @o a) === genericToJSON (options @o) a
  prop "encodes as aeson" $ \(a :: a) ->
    decode (encodingToLazyByteString (jsonEncode (By @o a)))
      === Just (genericToJSON (options @o) a)
  prop "parses what aeson prints" $ \(a :: a) ->
    jsonParse (genericToJSON (options @o) a) === Right (By @o a)

jsonOptionsSpec :: Spec
jsonOptionsSpec = describe "jsonGeneric" $ do
  agreesByOptions @Defaults @Sample "defaultOptions"
  agreesByOptions @Untagged @Sample "UntaggedValue"
  agreesByOptions @SingleField @Sample "ObjectWithSingleField"
  agreesByOptions @TwoElements @Sample "TwoElemArray"
  agreesByOptions @Tweaked @Sample "tweaked options"
  agreesByOptions @Tweaked @Lone "a single field, tweaked"
  agreesByOptions @Tweaked @Hue "an enumeration, tweaked"
  agreesByOptions @Defaults @Hue "an enumeration"
  it "parses an omitted field" $
    jsonParse @(By Defaults Sample)
      (object ["tag" .= ("Record" :: Text), "recordInt" .= (1 :: Int)])
      `shouldBe` Right (By (Record 1 Nothing))
