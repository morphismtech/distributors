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
  , jsonTupleSpec
  , jsonTupleTypeSpec
  , jsonOptionalSpec
  , jsonCodecSpec
  , jsonPrintSpec
  ) where

import Control.Lens (prism')
import Control.Lens.Grammar
  ( dimap, lmap, manyP, oneP, optionalP, rule
  , (>*<), (>+<), (>?)
  )
import Control.Lens.Grammar.Json
import Data.Aeson
  ( FromJSON (..), ToJSON (..), Value (String), decode
  , object, (.=)
  )
import Data.Aeson.Encoding (encodingToLazyByteString)
import Data.Aeson.Key (Key)
import Data.Aeson.KeyMap (KeyMap)
import Data.Aeson.Types (DotNetTime (..), formatError, parseEither)
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
import Test.QuickCheck hiding (Fixed)
import Test.QuickCheck.Instances ()

jsonTypeOf :: forall a. Json a => TsType
jsonTypeOf = tsRootType (jsonType a)

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
  json = dimap (\(Dup p) -> p) Dup
    (jsonObject (jsonKeyVal "k" json >*< jsonKeyVal "k" json))

jsonObjectSpec :: Spec
jsonObjectSpec = describe "jsonObject" $ do
  it "doesn't print overlapping keys" $
    printError (Dup (1, 2)) `shouldBe`
      Left "Error in $: cannot print key \"k\" twice"
  it "doesn't parse a key twice" $
    parseError @Dup (object ["k" .= (1 :: Int)]) `shouldBe`
      "Error in $: expected another key \"k\", but found {\"k\":1}"
  it "doesn't type overlapping keys" $
    tsRootType (jsonType (type Dup)) `shouldBe` TsUnion []
  it "ignores extra keys" $
    jsonParse @Point
      (object ["px" .= (1 :: Int), "py" .= (2 :: Int), "pz" .= (3 :: Int)])
      `shouldSatisfy` isRight

-- | A tuple of a number and rest strings, @[number, ...string[]]@.
newtype Rest = Rest (Scientific, [Text])
  deriving stock (Eq, Show)
instance Json Rest where
  json = dimap (\(Rest p) -> p) Rest $ jsonTuple $
    (,) <$> lmap fst (jsonVal json) <*> lmap snd (manyP (jsonVal json))

-- | Leading rest strings and a number, @[...string[], number]@.
newtype Leading = Leading ([Text], Scientific)
  deriving stock (Eq, Show)
instance Json Leading where
  json = dimap (\(Leading p) -> p) Leading $ jsonTuple $
    (,) <$> lmap fst (manyP (jsonVal json)) <*> lmap snd (jsonVal json)

-- | A number and an optional string, @[number, string?]@.
newtype Trailing = Trailing (Scientific, Maybe Text)
  deriving stock (Eq, Show)
instance Json Trailing where
  json = dimap (\(Trailing p) -> p) Trailing $ jsonTuple $
    (,) <$> lmap fst (jsonVal json) <*> lmap snd (optionalP (jsonVal json))

-- | An optional string before a number, @[number] | [string, number]@.
newtype Before = Before (Maybe Text, Scientific)
  deriving stock (Eq, Show)
instance Json Before where
  json = dimap (\(Before p) -> p) Before $ jsonTuple $
    (,) <$> lmap fst (optionalP (jsonVal json)) <*> lmap snd (jsonVal json)

-- | Two rests, @[...(number | string)[]]@.
newtype Rests = Rests ([Scientific], [Text])
  deriving stock (Eq, Show)
instance Json Rests where
  json = dimap (\(Rests p) -> p) Rests $ jsonTuple $
    (,) <$> lmap fst (manyP (jsonVal json)) <*> lmap snd (manyP (jsonVal json))

-- | Alternative elements, @[number] | [string]@.
newtype Alternative = Alternative (Either Scientific Text)
  deriving stock (Eq, Show)
instance Json Alternative where
  json = dimap (\(Alternative e) -> e) Alternative $
    jsonTuple (jsonVal json >+< jsonVal json)

-- | Round trip a `Value` through a `Json` grammar.
roundTrip :: forall a. (Json a, Eq a, Show a) => Value -> a -> Expectation
roundTrip value a = do
  jsonParse @a value `shouldBe` Right a
  jsonPrint a `shouldBe` Right value

jsonTupleSpec :: Spec
jsonTupleSpec = describe "variadic jsonTuple" $ do
  it "has rest elements" $ do
    roundTrip (toJSON [toJSON (1 :: Int)]) (Rest (1, []))
    roundTrip (toJSON [toJSON (1 :: Int), "a", "b"]) (Rest (1, ["a", "b"]))
    tsRootType (jsonType (type Rest)) `shouldBe`
      TsTuple [TsRequired TsNumber, TsRest TsString]
  it "backtracks leading rest elements" $ do
    roundTrip (toJSON [toJSON (1 :: Int)]) (Leading ([], 1))
    roundTrip (toJSON ["a", "b", toJSON (1 :: Int)]) (Leading (["a", "b"], 1))
    tsRootType (jsonType (type Leading)) `shouldBe`
      TsTuple [TsRest TsString, TsRequired TsNumber]
  it "has optional elements" $ do
    roundTrip (toJSON [toJSON (1 :: Int)]) (Trailing (1, Nothing))
    roundTrip (toJSON [toJSON (1 :: Int), "a"]) (Trailing (1, Just "a"))
    tsRootType (jsonType (type Trailing)) `shouldBe`
      TsTuple [TsRequired TsNumber, TsOptional TsString]
  it "expands optional elements before required elements" $ do
    roundTrip (toJSON [toJSON (1 :: Int)]) (Before (Nothing, 1))
    roundTrip (toJSON ["a", toJSON (1 :: Int)]) (Before (Just "a", 1))
    tsRootType (jsonType (type Before)) `shouldBe` TsUnion
      [ TsTuple [TsRequired TsNumber]
      , TsTuple [TsRequired TsString, TsRequired TsNumber]
      ]
  it "merges rest elements" $ do
    roundTrip (toJSON [toJSON (1 :: Int), toJSON (2 :: Int), "a"])
      (Rests ([1, 2], ["a"]))
    tsRootType (jsonType (type Rests)) `shouldBe`
      TsTuple [TsRest (TsUnion [TsNumber, TsString])]
  it "has alternative elements" $ do
    roundTrip (toJSON [toJSON (1 :: Int)]) (Alternative (Left 1))
    roundTrip (toJSON [String "a"]) (Alternative (Right "a"))
    tsRootType (jsonType (type Alternative)) `shouldBe` TsUnion
      [TsTuple [TsRequired TsNumber], TsTuple [TsRequired TsString]]
  it "locates failures in rest elements" $
    parseError @Rest (toJSON [toJSON (1 :: Int), "a", toJSON (2 :: Int)])
      `shouldBe` "Error in $[2]: expected string, but found 2"
  it "reports lengths" $
    parseError @Trailing (toJSON [toJSON (1 :: Int), "a", "b"]) `shouldBe`
      "Error in $: expected 2 elements or 1 element, \
      \but found [1,\"a\",\"b\"]"

-- | Random tuple grammars, of numbers and strings.
data TupG = TupNum | TupStr | TupOne | TupSeq TupG TupG | TupAlt TupG TupG
  | TupOpt TupG | TupMany TupG
  deriving stock Show

-- | A `TupG` promoted to a `Json` instance.
class TupGrammar (g :: TupG) where
  tupGrammar :: JsonTup q => q () ()
instance TupGrammar 'TupNum where
  tupGrammar = dimap (const 0) (const ()) (jsonVal jsonNumber)
instance TupGrammar 'TupStr where
  tupGrammar = dimap (const "") (const ()) (jsonVal jsonString)
instance TupGrammar 'TupOne where
  tupGrammar = oneP
instance (TupGrammar g0, TupGrammar g1) => TupGrammar ('TupSeq g0 g1) where
  tupGrammar = dimap (const ((), ())) (const ())
    (tupGrammar @g0 >*< tupGrammar @g1)
instance (TupGrammar g0, TupGrammar g1) => TupGrammar ('TupAlt g0 g1) where
  tupGrammar = dimap (const (Left ())) (const ())
    (tupGrammar @g0 >+< tupGrammar @g1)
instance TupGrammar g => TupGrammar ('TupOpt g) where
  tupGrammar = dimap (const Nothing) (const ()) (optionalP (tupGrammar @g))
instance TupGrammar g => TupGrammar ('TupMany g) where
  tupGrammar = dimap (const []) (const ()) (manyP (tupGrammar @g))

newtype Tup (g :: TupG) = Tup ()
  deriving stock Show
instance TupGrammar g => Json (Tup g) where
  json = dimap (const ()) Tup (jsonTuple (tupGrammar @g))

-- | A random `TupG`, both as a value and as a type.
data SomeTup = forall g. TupGrammar g => SomeTup TupG (Proxy g)
instance Show SomeTup where
  show (SomeTup g _) = show g
instance Arbitrary SomeTup where
  arbitrary = sized go
    where
      go n
        | n <= 1 = leaf
        | otherwise = frequency
          [ (2, leaf)
          , (3, sequenced <$> go (n `div` 2) <*> go (n `div` 2))
          , (2, alternated <$> go (n `div` 2) <*> go (n `div` 2))
          , (2, optional' <$> go (n - 1))
          , (1, many' <$> go (n - 1))
          ]
      leaf = elements
        [ SomeTup TupNum (Proxy @'TupNum)
        , SomeTup TupStr (Proxy @'TupStr)
        , SomeTup TupOne (Proxy @'TupOne)
        ]
      sequenced (SomeTup t0 (_ :: Proxy g0)) (SomeTup t1 (_ :: Proxy g1)) =
        SomeTup (TupSeq t0 t1) (Proxy @('TupSeq g0 g1))
      alternated (SomeTup t0 (_ :: Proxy g0)) (SomeTup t1 (_ :: Proxy g1)) =
        SomeTup (TupAlt t0 t1) (Proxy @('TupAlt g0 g1))
      optional' (SomeTup t (_ :: Proxy g)) =
        SomeTup (TupOpt t) (Proxy @('TupOpt g))
      many' (SomeTup t (_ :: Proxy g)) =
        SomeTup (TupMany t) (Proxy @('TupMany g))

hasMany :: TupG -> Bool
hasMany = \case
  TupMany _ -> True
  TupSeq g0 g1 -> hasMany g0 || hasMany g1
  TupAlt g0 g1 -> hasMany g0 || hasMany g1
  TupOpt g -> hasMany g
  _ -> False

-- | The remainders after a grammar matches a prefix of a sequence.
tupMatches :: TupG -> [TsType] -> [[TsType]]
tupMatches g ts = case g of
  TupNum -> [rest | TsNumber : rest <- [ts]]
  TupStr -> [rest | TsString : rest <- [ts]]
  TupOne -> [ts]
  TupSeq g0 g1 -> concatMap (tupMatches g1) (tupMatches g0 ts)
  TupAlt g0 g1 -> tupMatches g0 ts <> tupMatches g1 ts
  TupOpt g0 -> ts : tupMatches g0 ts
  TupMany g0 -> ts : concat
    [ tupMatches (TupMany g0) rest
    | rest <- tupMatches g0 ts, length rest < length ts ]

tupAccepts :: TupG -> [TsType] -> Bool
tupAccepts g ts = [] `elem` tupMatches g ts

-- | Does a TypeScript tuple type accept a sequence of element types?
tsAccepts :: TsType -> [TsType] -> Bool
tsAccepts ty ts = case ty of
  TsUnion alternatives -> any (`tsAccepts` ts) alternatives
  TsTuple els -> go els ts
  _ -> False
  where
    is t0 t1 = case t0 of
      TsUnion alternatives -> any (`is` t1) alternatives
      _ -> t0 == t1
    go [] rest = null rest
    go (el : els) rest = case (el, rest) of
      (TsRequired t, t1 : rest') -> is t t1 && go els rest'
      (TsRequired _, []) -> False
      (TsOptional t, _) -> go els rest || go (TsRequired t : els) rest
      (TsRest t, _) -> go els rest || case rest of
        t1 : rest' -> is t t1 && go (el : els) rest'
        [] -> False

-- | TypeScript's @checkTupleType@ restrictions on tuple types.
tsValid :: TsType -> Bool
tsValid = \case
  TsUnion alternatives -> all tsValid alternatives
  TsTuple els -> go False False els
  _ -> True
  where
    go _ _ [] = True
    go optional rest (el : els) = case el of
      TsRest _ -> not rest && go optional True els
      TsOptional _ -> not rest && go True rest els
      TsRequired _ -> not optional && go optional rest els

-- | A JSON array of a sequence of element types.
tupValue :: [TsType] -> Value
tupValue = toJSON . map (\case TsNumber -> toJSON (0 :: Int); _ -> String "")

jsonTupleTypeSpec :: Spec
jsonTupleTypeSpec = describe "variadic jsonTuple types" $ do
  let
    sequences = listOf (elements [TsNumber, TsString])
    -- the reference matcher & optional expansion are exponential
    small :: Testable prop => prop -> Property
    small = mapSize (min 12)
  it "are valid TypeScript" $ property $ small $
    \(SomeTup _ (_ :: Proxy g)) ->
      tsValid (tsRootType (jsonType (type (Tup g))))
  it "parse exactly the sequences the grammar does" $ property $ small $
    \(SomeTup t (_ :: Proxy g)) -> forAll sequences $ \ts ->
      tupAccepts t ts
        === isRight (jsonParse @(Tup g) (tupValue ts))
  it "accept every sequence the grammar does" $ property $ small $
    \(SomeTup t (_ :: Proxy g)) -> forAll sequences $ \ts ->
      tupAccepts t ts ==> tsAccepts (tsRootType (jsonType (type (Tup g)))) ts
  it "accept exactly the sequences the grammar does, without manyP" $
    property $ small $ \(SomeTup t (_ :: Proxy g)) ->
      not (hasMany t) ==> forAll sequences $ \ts ->
        tupAccepts t ts === tsAccepts (tsRootType (jsonType (type (Tup g)))) ts

-- | A partial grammar, which can't print `Uncovered`.
data Partial = Covered Scientific | Uncovered
  deriving stock (Eq, Show)
instance Json Partial where
  json = rule "Partial" $
    prism' Covered (\case Covered n -> Just n; _ -> Nothing) >? json

jsonPrintSpec :: Spec
jsonPrintSpec = describe "jsonPrint errors" $ do
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

-- | A complete type definition, named @start@ with @rules@.
definesType
  :: forall a. Json a => String -> [(String, TsType)] -> Expectation
definesType start rules =
  jsonType a `shouldBe` TsDeclarations (TsAlias start) (Map.fromList rules)

jsonTypeSpec :: Spec
jsonTypeSpec = describe "jsonType" $ do
  let
    point = TsObject
      [TsProperty "px" False TsNumber, TsProperty "py" False TsNumber]
    tagged tag props = TsObject (TsProperty "tag" False (TsLiteral tag) : props)
  it "encodes basic types" $ do
    jsonTypeOf @Bool `shouldBe` TsBoolean
    jsonTypeOf @Text `shouldBe` TsString
    jsonTypeOf @Scientific `shouldBe` TsNumber
  it "encodes containers" $ do
    jsonTypeOf @(Vector Text) `shouldBe` TsArray TsString
    jsonTypeOf @(Maybe Text) `shouldBe` TsUnion [TsNull, TsString]
    jsonTypeOf @(Map Text Scientific) `shouldBe` TsDict TsNumber
  it "defines a record as an object" $
    definesType @Point "Point" [("Point", point)]
  it "defines a single-field constructor as its contents" $
    definesType @Wrap "Wrap" [("Wrap", TsNumber)]
  it "defines a positional multi-field constructor as a tuple" $
    definesType @Pair "Pair"
      [("Pair", TsTuple [TsRequired TsNumber, TsRequired TsString])]
  it "defines a nullary single-constructor type as an empty tuple" $
    definesType @Unit "Unit" [("Unit", TsTuple [])]
  it "defines an all-nullary sum as a union of string literals" $
    definesType @Color "Color"
      [ ("Color"
        , TsUnion [TsLiteral "Red", TsLiteral "Green", TsLiteral "Blue"])
      ]
  it "defines a mixed sum as a discriminated union of objects" $
    definesType @Shape "Shape"
      [ ( "Shape"
        , TsUnion
          [ tagged "Circle" [TsProperty "contents" False TsNumber]
          , tagged "Square" [TsProperty "_side" False TsNumber]
          ]
        )
      ]
  it "defines nested records" $
    definesType @Profile "Profile"
      [ ("Profile", TsObject
          [ TsProperty "name" False TsString
          , TsProperty "tags" False (TsArray TsString)
          , TsProperty "nickname" False (TsUnion [TsNull, TsString])
          ])
      ]
  it "defines a recursive type" $
    definesType @Peano "Peano"
      [ ( "Peano"
        , TsUnion
          [ tagged "Zero" []
          , tagged "Succ" [TsProperty "contents" False (TsAlias "Peano")]
          ]
        )
      ]
  it "defines mutually recursive types" $ do
    let
      rules =
        [ ("Forest", TsArray (TsAlias "Branch"))
        , ("Branch"
          , TsTuple [TsRequired TsNumber, TsRequired (TsAlias "Forest")])
        ]
    definesType @Forest "Forest" rules
    definesType @Branch "Branch" rules
  it "defines each instantiation of a parametric type" $
    definesType @(Box (Box Scientific)) "Box (Box Scientific)"
      [ ("Box (Box Scientific)", TsAlias "Box Scientific")
      , ("Box Scientific", TsNumber)
      ]
  it "defines recursive non-generic types" $ do
    definesType @(Tree Scientific) "Tree Scientific"
      [ ("Tree Scientific"
        , TsTuple
          [ TsRequired TsNumber
          , TsRequired (TsArray (TsAlias "Tree Scientific"))
          ])
      ]
    let
      fixRules =
        [ ( "Fix (Either Scientific)"
          , TsUnion
            [ TsObject [TsProperty "Left" False TsNumber]
            , TsObject
              [ TsProperty "Right" False
                  (TsAlias "Fix (Either Scientific)")
              ]
            ]
          )
        ]
    definesType @(Fix (Either Scientific)) "Fix (Either Scientific)" fixRules
    definesType @(Mu (Either Scientific)) "Fix (Either Scientific)" fixRules
    definesType @(Nu (Either Scientific)) "Fix (Either Scientific)" fixRules
    let value = TsAlias "Value"
    definesType @Value "Value"
      [ ("Value", TsUnion
          [ TsNull, TsBoolean, TsNumber, TsString
          , TsArray value, TsDict value
          ])
      ]
  it "nests type definitions" $
    jsonType (type (Vector Point)) `shouldBe`
      TsDeclarations
        (TsArray (TsAlias "Point")) (Map.fromList [("Point", point)])
  it "defines each type once" $
    Map.size (tsTypeAliases (jsonType (type Twice16))) `shouldBe` 16
  it "names colliding definitions uniquely" $
    jsonType (type Collide) `shouldBe` TsDeclarations (TsAlias "Collide")
      (Map.fromList
        [ ("Collide", TsObject
            [ TsProperty "named" False (TsAlias "Point")
            , TsProperty "typed" False (TsAlias "Properties.Json.Point")
            ])
        , ("Point", TsNumber)
        , ("Properties.Json.Point", point)
        ])
  it "renders TypeScript" $ do
    jsonTypeScript (type Point) `shouldBe`
      "export type Point = { px: number; py: number };\n"
    jsonTypeScript Shape `shouldBe` Text.unlines
      [ "export type Shape = { tag: \"Circle\"; contents: number } \
        \| { tag: \"Square\"; _side: number };" ]
    jsonTypeScript (type (Box (Box Scientific))) `shouldBe` Text.unlines
      [ "export type Box_Box_Scientific = Box_Scientific;"
      , "export type Box_Scientific = number;"
      ]
    jsonTypeScript (type (Maybe [Text])) `shouldBe`
      "export type Maybe_List_Text = null | string[];\n"
    jsonTypeScript (type Optional) `shouldBe`
      "export type Optional = { a: number; \"b c\"?: string | number };\n"
    jsonTypeScript (type Trailing) `shouldBe`
      "export type Trailing = [number, string?];\n"

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
  json = jsonRule $ jsonObject $ Collide
    <$> lmap named (jsonKeyVal "named" (rule "Point" jsonNumber))
    <*> lmap typed (jsonKeyVal "typed" json)

-- | An optional property, with a key which isn't an identifier.
data Optional = Optional Scientific (Maybe (Either Text Scientific))
  deriving stock (Eq, Show)
instance Json Optional where
  json = jsonRule $ jsonObject $ Optional
    <$> lmap (\(Optional a _) -> a) (jsonKeyVal "a" json)
    <*> lmap (\(Optional _ b) -> b)
      (jsonOptionalKeyVal "b c" (jsonString >+< jsonNumber))

jsonOptionalSpec :: Spec
jsonOptionalSpec = describe "jsonOptionalKeyVal" $ do
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
  codecCompat @Profile (Profile <$> arbitrary <*> arbitrary <*> arbitrary)
  codecCompat @(Map Text [Int]) arbitrary
  codecCompat @(Int, Maybe Bool, Text) arbitrary
  codecCompat @Value arbitrary
  codecCompat @Shape (oneof [Circle <$> arbitrary, Square <$> arbitrary])
  codecCompat @Color arbitraryBoundedEnum
  it "encodes in order" $
    encodingToLazyByteString <$> jsonEncode (Point 1 2)
      `shouldBe` Right "{\"px\":1,\"py\":2}"

codecCompat :: forall a. (Json a, ToJSON a, Show a, Typeable a) => Gen a -> Spec
codecCompat gen = it (show (typeRep (Proxy @a))) $ forAll gen $ \a ->
  (decode . encodingToLazyByteString <$> jsonEncode a)
    === Right (Just (toJSON a))

-- | The error message of parsing a `Value`.
parseError :: forall a. (Json a, Show a) => Value -> String
parseError = either errorText show . jsonParse @a

-- | The error message of printing a value.
printError :: Json a => a -> Either String Value
printError = either (Left . errorText) Right . jsonPrint

errorText :: JsonError -> String
errorText err = formatError (jsonErrorPath err) (jsonErrorMessage err)

jsonErrorSpec :: Spec
jsonErrorSpec = describe "jsonParse errors" $ do
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
  in jsonPrint a === Right value
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
