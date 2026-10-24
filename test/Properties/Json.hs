{-# LANGUAGE DeriveAnyClass #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE OverloadedStrings #-}
module Properties.Json
  ( jsonTypeSpec
  , aesonSpec
  , aesonCompat
  , aesonEncodeCompat
  ) where

import Control.Lens.Grammar (Bnf (..))
import Control.Lens.Grammar.Json
import Data.Aeson (FromJSON (..), FromJSONKey, ToJSON (..), ToJSONKey, Value)
import Data.Aeson.Key (Key)
import Data.Aeson.KeyMap (KeyMap)
import Data.Aeson.Types (DotNetTime (..), parseEither)
import Data.DList (DList)
import Data.DList qualified as DList
import Data.DList.DNonEmpty (DNonEmpty)
import Data.DList.DNonEmpty qualified as DNonEmpty
import Data.Either (isLeft)
import Data.Fix (Fix (..), Mu, Nu, unfoldMu, unfoldNu)
import Data.Fixed (Milli)
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
import Data.Set qualified as Set
import Data.Set (Set)
import Data.Strict qualified as Strict
import Data.Tagged (Tagged)
import Data.Text (Text)
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
import Data.Tree (Tree)
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
import GHC.Generics (Generic, Generically (..))
import Network.URI (URI, parseURI)
import Numeric.Natural (Natural)
import Test.Hspec
import Test.QuickCheck
import Test.QuickCheck.Instances ()

-- | Compare `TextMap` against @aeson@'s textual-key `Map` encoding.
deriving newtype instance (ToJSONKey str, ToJSON val)
  => ToJSON (TextMap str val)
deriving newtype instance (Ord str, FromJSONKey str, FromJSON val)
  => FromJSON (TextMap str val)

jsonTypeOf :: forall a. Json a => TsType
jsonTypeOf = startBnf (jsonType @a)

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
  | Square { side :: Scientific }
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

-- | A complete type definition, named @start@ with @rules@.
definesType
  :: forall a. Json a => String -> [(String, TsType)] -> Expectation
definesType start rules =
  jsonType @a `shouldBe` Bnf (TsNonTerminal start) (Set.fromList rules)

jsonTypeSpec :: Spec
jsonTypeSpec = describe "jsonType" $ do
  it "encodes basic types" $ do
    jsonTypeOf @Bool `shouldBe` TsBoolean
    jsonTypeOf @Text `shouldBe` TsString
    jsonTypeOf @Scientific `shouldBe` TsNumber
  it "encodes containers" $ do
    jsonTypeOf @(Vector Text) `shouldBe` TsArray TsString
    jsonTypeOf @(Maybe Text) `shouldBe` TsUnion TsNull TsString
    jsonTypeOf @(TextMap Text Scientific) `shouldBe` TsDict TsNumber
  it "defines a record as an object" $
    definesType @Point "Point"
      [("Point", TsObject [("px", TsNumber), ("py", TsNumber)])]
  it "defines a single-field constructor as its contents" $
    definesType @Wrap "Wrap" [("Wrap", TsNumber)]
  it "defines a positional multi-field constructor as a tuple" $
    definesType @Pair "Pair" [("Pair", TsTuple [TsNumber, TsString])]
  it "defines a nullary single-constructor type as an empty tuple" $
    definesType @Unit "Unit" [("Unit", TsTuple [])]
  it "defines an all-nullary sum as a string" $
    definesType @Color "Color" [("Color", TsString)]
  it "defines a mixed sum as a tagged union of objects" $
    definesType @Shape "Shape"
      [ ("Shape", TsUnion
          (TsObject [("tag", TsString), ("contents", TsNumber)])
          (TsObject [("tag", TsString), ("side", TsNumber)]))
      ]
  it "defines nested records" $
    definesType @Profile "Profile"
      [ ("Profile", TsObject
          [ ("name", TsString)
          , ("tags", TsArray TsString)
          , ("nickname", TsUnion TsNull TsString)
          ])
      ]
  it "defines a recursive type" $
    definesType @Peano "Peano"
      [ ("Peano", TsUnion
          (TsObject [("tag", TsString)])
          (TsObject [("tag", TsString), ("contents", TsNonTerminal "Peano")]))
      ]
  it "defines mutually recursive types" $ do
    let
      rules =
        [ ("Forest", TsArray (TsNonTerminal "Branch"))
        , ("Branch", TsTuple [TsNumber, TsNonTerminal "Forest"])
        ]
    definesType @Forest "Forest" rules
    definesType @Branch "Branch" rules
  it "defines each instantiation of a parametric type" $
    definesType @(Box (Box Scientific)) "Box (Box Scientific)"
      [ ("Box (Box Scientific)", TsNonTerminal "Box Scientific")
      , ("Box Scientific", TsNumber)
      ]
  it "defines recursive non-generic types" $ do
    definesType @(Tree Scientific) "Tree Scientific"
      [ ("Tree Scientific"
        , TsTuple [TsNumber, TsArray (TsNonTerminal "Tree Scientific")])
      ]
    let
      fixRules =
        [ ("Fix (Either Scientific)", TsUnion
            (TsObject [("Left", TsNumber)])
            (TsObject [("Right", TsNonTerminal "Fix (Either Scientific)")]))
        ]
    definesType @(Fix (Either Scientific)) "Fix (Either Scientific)" fixRules
    definesType @(Mu (Either Scientific)) "Fix (Either Scientific)" fixRules
    definesType @(Nu (Either Scientific)) "Fix (Either Scientific)" fixRules
    let value = TsNonTerminal "Value"
    definesType @Value "Value"
      [ ("Value", foldr1 TsUnion
          [ TsNull, TsBoolean, TsNumber, TsString
          , TsArray value, TsDict value
          ])
      ]
  it "nests type definitions" $
    jsonType @(Vector Point) `shouldBe` Bnf
      (TsArray (TsNonTerminal "Point"))
      (Set.fromList [("Point", TsObject [("px", TsNumber), ("py", TsNumber)])])

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
      .&&. fmap toJSON (parseEither (jsonParse @a) value)
        === fmap toJSON (parseEither (parseJSON @a) value)

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
  in jsonPrint a === Just value
    .&&. fmap toJSON (parseEither (jsonParse @a) value) === Right value

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
    parseEither (jsonParse @Void) (toJSON ()) `shouldSatisfy` isLeft
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
  aesonCompat @(TextMap Text Int) (TextMap <$> arbitrary)
  aesonCompat @(TextMap String Int) (TextMap <$> arbitrary)
  aesonCompat @(TextMap LText.Text Int) (TextMap <$> arbitrary)
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
