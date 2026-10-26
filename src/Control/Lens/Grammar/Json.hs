{-# LANGUAGE OverloadedStrings, RequiredTypeArguments #-}

module Control.Lens.Grammar.Json
  ( -- * Json
    Json (..)
  , jsonParse
  , jsonDecode
  , jsonPrint
  , jsonPrintError
  , jsonEncode
  , jsonEncodeError
  , jsonTypes
    -- * Grammar
  , JsonVal (..)
  , JsonStr (..)
  , JsonTup (..)
  , JsonObj (..)
    -- * Errors
  , JsonError (..)
  , JsonErrorSort (..)
  , jsonErrorMessage
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.Grammar
import Control.Monad
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Reader (ReaderT, ask, local, runReaderT)
import Control.Monad.Trans.State.Strict
import Data.Aeson qualified as Aeson
import Data.Aeson.Encoding (Encoding)
import Data.Aeson.Encoding qualified as Encoding
import Data.Aeson.Key (Key)
import Data.Aeson.Key qualified as Key
import Data.Aeson.KeyMap (KeyMap)
import Data.Aeson.KeyMap qualified as KeyMap
import Data.Aeson.Text (encodeToLazyText)
import Data.Aeson.Types
  (DotNetTime (..), JSONPathElement (..), Object, Value (..))
import Data.Char (isAlpha, isAlphaNum, isDigit)
import Data.ByteString.Builder qualified as Builder
import Data.ByteString.Lazy qualified as LByteString
import Data.Coerce
import Data.DList (DList)
import Data.DList qualified as DList
import Data.DList.DNonEmpty (DNonEmpty)
import Data.DList.DNonEmpty qualified as DNonEmpty
import Data.Fix (Fix (..), Mu, Nu, foldMu, foldNu, unfoldMu, unfoldNu)
import Data.Fixed (Fixed, HasResolution (..), Nano)
import Data.Foldable (toList, traverse_)
import Data.Function (fix)
import Data.Functor.Compose (Compose (..))
import Data.Functor.Product qualified as Functor
import Data.Functor.Sum qualified as Functor
import Data.Functor.These (These1 (..))
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HashMap
import Data.HashSet (HashSet)
import Data.HashSet qualified as HashSet
import Data.Hashable (Hashable)
import Data.Int (Int8, Int16, Int32, Int64)
import Data.IntMap (IntMap)
import Data.IntMap qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.Kind
import Data.List (find, findIndices, intercalate, nub, stripPrefix)
import Data.List.NonEmpty (NonEmpty, nonEmpty)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe
import Data.Monoid (Ap (..))
import Data.Monoid qualified as Monoid
import Data.Ord (Down (..))
import Data.Primitive.Array (Array)
import Data.Primitive.PrimArray (PrimArray)
import Data.Primitive.SmallArray (SmallArray)
import Data.Primitive.Types (Prim)
import Data.Profunctor
import Data.Profunctor.Unsafe ((#.), (.#))
import Data.Proxy (Proxy (..))
import Data.Ratio (Ratio, denominator, numerator, (%))
import Data.Scientific
import Data.SOP (All, K (..), NP, hcollapse, hcpure)
import Data.Semigroup qualified as Semigroup
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Strict qualified as Strict
import Data.String (IsString (..))
import Data.Tagged (Tagged (..))
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import Data.Text.Read qualified as TextRead
import Data.Text.Unsafe qualified as Text (lengthWord8)
import Data.Text.Lazy qualified as LText
import Data.Text.Short (ShortText)
import Data.Text.Short qualified as ShortText
import Data.These (These (..))
import Data.Time
  ( CalendarDiffDays (..), CalendarDiffTime (..), Day, DayOfWeek (..)
  , DiffTime, LocalTime, NominalDiffTime, TimeOfDay, UTCTime, ZonedTime
  , defaultTimeLocale, formatTime, parseTimeM
  )
import Data.Time.Calendar.Month (Month)
import Data.Time.Calendar.Quarter (Quarter, QuarterOfYear (..))
import Data.Time.Clock.System (SystemTime (..))
import Data.Time.FromText qualified as TimeText
import Data.Traversable (for)
import Data.Tree (Forest, Tree (..))
import Data.Tuple (Solo (MkSolo), getSolo)
import Data.UUID.Types (UUID)
import Data.UUID.Types qualified as UUID
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Data.Vector.Mutable qualified as MVector
import Data.Vector.Generic qualified as VG
import Data.Vector.Primitive qualified as VP
import Data.Vector.Storable qualified as VS
import Data.Vector.Unboxed qualified as VU
import Data.Version (Version, parseVersion, showVersion)
import Data.Void (Void, absurd)
import Data.Word (Word8, Word16, Word32, Word64)
import Foreign.C.Types (CTime (..))
import Foreign.Storable (Storable)
import GHC.Exts qualified as Exts
import GHC.Generics qualified as GHC
import Network.URI (URI)
import Network.URI qualified as URI
import Numeric.Natural (Natural)
import Text.Read (readMaybe)
import Text.ParserCombinators.ReadP (readP_to_S)
import Type.Reflection

makePrisms ''Value

-- Json grammars --

class Json a where

  json :: JsonVal p => p a a
  default json :: (Json (GHC.Generically a), JsonVal p) => p a a
  json = iso GHC.Generically coerce >~ json

  {- | `Data.Aeson.toJSONList` -}
  jsonList :: JsonVal p => p [a] [a]
  jsonList = jsonArray json

  {- | `Data.Aeson.toJSONKey` -}
  jsonKeyMap :: (Json v, JsonVal p) => p [(a, v)] [(a, v)]
  jsonKeyMap = jsonArray (jsonTuple (jsonElem json >*< jsonElem json))

  {- | `Data.Aeson.toJSONKeyList` -}
  jsonKeyListMap :: (Json v, JsonVal p) => p [([a], v)] [([a], v)]
  jsonKeyListMap = jsonArray (jsonTuple (jsonElem jsonList >*< jsonElem json))

-- Running Json grammars --

-- | `Data.Aeson.parseJSON`
jsonParse :: Json a => Value -> Either JsonError a
jsonParse = runJsonParsor json

-- | `Data.Aeson.decode`
jsonDecode :: Json a => LByteString.ByteString -> Maybe a
jsonDecode = Aeson.decode >=> either (\_ -> Nothing) Just . jsonParse

-- | `Data.Aeson.toJSON`
jsonPrint :: Json a => a -> Value
jsonPrint = either (\_ -> Null) id . jsonPrintError

jsonPrintError :: Json a => a -> Either JsonError Value
jsonPrintError = runJsonPrintor json

-- | `Data.Aeson.toEncoding`
jsonEncode :: Json a => a -> Encoding
jsonEncode = either (\_ -> Encoding.null_) id . jsonEncodeError

jsonEncodeError :: Json a => a -> Either JsonError Encoding
jsonEncodeError = runJsonPrintor json

jsonTypes :: forall (as :: [Type]) -> All Json as => Text
jsonTypes as = renderTypeScript $ hcollapse
  (hcpure (Proxy @Json) tsRoot :: NP (K (TsGrammor () ())) as)
  where
    tsRoot :: forall a. Json a => K (TsGrammor () ()) a
    tsRoot = K (coerce (json @a @TsGrammor))

class
  ( CocartesianChoice p
  , JsonStr p
  , forall x y. BackusNaurForm (p x y)
  ) => JsonVal p where
  jsonNull :: p () ()
  jsonBool :: p Bool Bool
  jsonNumber :: p Scientific Scientific
  jsonInt :: p Int Int
  jsonInt = jsonBoundedInteger
  jsonInt8 :: p Int8 Int8
  jsonInt8 = jsonBoundedInteger
  jsonInt16 :: p Int16 Int16
  jsonInt16 = jsonBoundedInteger
  jsonInt32 :: p Int32 Int32
  jsonInt32 = jsonBoundedInteger
  jsonInt64 :: p Int64 Int64
  jsonInt64 = jsonBoundedInteger
  jsonWord :: p Word Word
  jsonWord = jsonBoundedInteger
  jsonWord8 :: p Word8 Word8
  jsonWord8 = jsonBoundedInteger
  jsonWord16 :: p Word16 Word16
  jsonWord16 = jsonBoundedInteger
  jsonWord32 :: p Word32 Word32
  jsonWord32 = jsonBoundedInteger
  jsonWord64 :: p Word64 Word64
  jsonWord64 = jsonBoundedInteger
  jsonDouble :: p Double Double
  jsonDouble = iso fromFloatDigits toRealFloat >~ jsonNumber
  jsonArray :: p a b -> p [a] [b]
  jsonDict
    :: (forall q. JsonStr q => q a b)
    -> p c d -> p [(a, c)] [(b, d)]
  jsonTuple :: (forall q. JsonTup p q => q a b) -> p a b
  jsonObject :: (forall q. JsonObj p q => q a b) -> p a b
  jsonValue :: p Value Value
  jsonValue = jsonTyped $ orP
    [ _Null >? jsonNull
    , _Bool >? jsonBool
    , _Number >? jsonNumber
    , _String >? jsonText
    , _Array . iso Vector.toList Vector.fromList >? jsonArray jsonValue
    , _Object . iso KeyMap.toList KeyMap.fromList >? jsonDict jsonKey jsonValue
    ]
  jsonTyped :: forall a. Typeable a => p a a -> p a a
  jsonTyped = rule (show (typeRep @a))

{- |
prop> fromString s = only s ?< jsonString
prop> jsonString = iso Text.pack Text.unpack >~ jsonText
-}
class
  ( Cochoice p
  , forall x y. (x ~ (), y ~ ()) => IsString (p x y)
  ) => JsonStr p where
  jsonText :: p Text Text
  jsonString :: p String String
  jsonString = iso Text.pack Text.unpack >~ jsonText
  {- | A string matched from its `Text`,
  which is reviewed as an @aeson@ string `Encoding.Encoding'`.
  -}
  jsonEncodedText :: APrism Text (Encoding.Encoding' Text) a a -> p a a
  jsonEncodedText encoding = withPrism encoding $ \encode match ->
    prism' (encodedText . encode) (either (const Nothing) Just . match)
      ?< jsonText

{- | `JsonTup` grammars describe the elements of a JSON array.
As `Alternator`s they have optional elements (`optionalP`, `optionP`),
rest elements (`manyP`, `someP`) and alternatives (`>+<`, `>|<`),
like TypeScript's variadic tuple types, @[A, B?, ...C[]]@.
Its elements are `JsonVal` grammars, which determine its type.
-}
class (JsonVal p, Alternator q) => JsonTup p q | q -> p where
  jsonElem :: p a b -> q a b

{- | `JsonObj` grammars describe the properties of a JSON object.
Each key may be read or written at most once.
A required property, @k !: v@, is like TypeScript's @{k: T}@,
and an optional property, @k ?: v@, may be missing, like @{k?: T}@.
Its properties are `JsonVal` grammars, which determine its type.
-}
class (JsonVal p, Monoidal q) => JsonObj p q | q -> p where
  (!:) :: Text -> p a b -> q a b
  (?:) :: Text -> p a b -> q (Maybe a) (Maybe b)
infixr 7 !:, ?:

-- Errors --

{- | A located failure to parse or print a `Value`.
Its path is relative to that `Value`, root first.
It expected one of the alternatives, none meaning just "unexpected".
Parsing found a `Value`; printing doesn't show the Haskell value it found.
It failed within `rule`s, outermost first, branching where alternatives
failed alike; a `rule` it failed for as a whole is its expectation instead.
-}
data JsonError = JsonError
  { jsonErrorPath :: [JSONPathElement]
  , jsonErrorExpected :: [String]
  , jsonErrorFound :: Maybe Value
  , jsonErrorSort :: JsonErrorSort
  , jsonErrorRules :: Forest String
  } deriving stock (Eq, Show)

data JsonErrorSort
  = JsonLiteral
  -- ^ a string literal mismatch; the alternative doesn't apply
  | JsonMismatch
  -- ^ the value was rejected as a whole
  | JsonMissing
  -- ^ the value was rejected for what it contains, lacks or repeats
  deriving stock (Eq, Ord, Show)

jsonErrorMessage :: JsonError -> String
jsonErrorMessage err = case (jsonErrorFound err, jsonErrorExpected err) of
  (Just found, []) -> "unexpected " <> render found
  (Just found, expected) ->
    "expected " <> alternatives expected <> ", but found " <> render found
  (Nothing, []) -> "cannot print"
  (Nothing, expected)
    | jsonErrorSort err == JsonMissing ->
        "cannot print " <> alternatives expected
    | otherwise -> "cannot print as " <> alternatives expected
  where
    render = abbreviate . LText.unpack . encodeToLazyText
    abbreviate str = if length str > 60 then take 57 str <> "..." else str
    alternatives = \case
      [] -> ""
      [e] -> e
      es -> intercalate ", " (init es) <> " or " <> last es

jsonUnexpected :: Maybe Value -> Either JsonError a
jsonUnexpected found = Left (JsonError [] [] found JsonMismatch [])

jsonMismatch :: String -> Value -> Either JsonError a
jsonMismatch expected found =
  Left (JsonError [] [expected] (Just found) JsonMismatch [])

jsonMissing :: String -> Maybe Value -> Either JsonError a
jsonMissing expected found =
  Left (JsonError [] [expected] found JsonMissing [])

countElements :: Int -> String
countElements n = show n <> if n == 1 then " element" else " elements"

jsonAt :: JSONPathElement -> Either JsonError a -> Either JsonError a
jsonAt el = onFailure (\err -> err {jsonErrorPath = el : jsonErrorPath err})

-- | Map a failure, sharing a success.
onFailure
  :: (JsonError -> JsonError) -> Either JsonError a -> Either JsonError a
onFailure f = \case
  Left err -> Left (f err)
  success -> success

-- | Map a success strictly, sharing a failure.
onSuccess :: (a -> b) -> Either JsonError a -> Either JsonError b
onSuccess f = \case
  Left err -> Left err
  Right a -> Right $! f a

{- | A `rule` labels its failures as a whole,
like @(\<?\>)@ for parser combinators, and encloses its other failures.
-}
jsonRelabel :: String -> JsonError -> JsonError
jsonRelabel name err
  | null (jsonErrorPath err)
  , jsonErrorSort err /= JsonMissing = err {jsonErrorExpected = [name]}
  | otherwise = err {jsonErrorRules = [Node name (jsonErrorRules err)]}

{- | Combine the failures of alternatives: the deepest failure wins,
failures on the same value merge their expectations & rules,
and a string literal mismatch loses to any other failure.
-}
jsonOrElse :: JsonError -> JsonError -> JsonError
jsonOrElse err1 err2
  | depth1 /= depth2 = if depth1 > depth2 then err1 else err2
  | jsonErrorPath err1 == jsonErrorPath err2
  , jsonErrorFound err1 == jsonErrorFound err2 = err2
    { jsonErrorExpected =
        nub (jsonErrorExpected err1 <> jsonErrorExpected err2)
    , jsonErrorSort = max (jsonErrorSort err1) (jsonErrorSort err2)
    , jsonErrorRules = jsonErrorRules err1 <> jsonErrorRules err2
    }
  | jsonErrorSort err2 == JsonLiteral
  , jsonErrorSort err1 /= JsonLiteral = err1
  | otherwise = err2
  where
    depth1 = length (jsonErrorPath err1)
    depth2 = length (jsonErrorPath err2)

-- Parsing interpreters --

{- | `JsonParsor` parses a `Value`. It may also have a `Dispatch`,
when it only accepts string literals, as values or as the values of
a key of objects, so that alternatives are chosen by lookup,
rather than tried in turn.
-}
data JsonParsor a b = JsonParsor
  { jsonParsorDispatch :: Maybe (Dispatch b)
  , runJsonParsor :: Value -> Either JsonError b
  }

{- | Parsers by the string literal which they accept,
as the value itself, or as the value of a key.
-}
data Dispatch b = Dispatch
  { dispatchKey :: Maybe Key
  , dispatchTable :: Map Text (Value -> Either JsonError b)
  }

jsonParsor :: (Value -> Either JsonError b) -> JsonParsor a b
jsonParsor = JsonParsor Nothing

-- | Transform a parser and its dispatch table alike.
mapParsing
  :: ((Value -> Either JsonError b) -> Value -> Either JsonError c)
  -> JsonParsor a b -> JsonParsor x c
mapParsing f parsor = JsonParsor
  { jsonParsorDispatch = retable <$> jsonParsorDispatch parsor
  , runJsonParsor = f (runJsonParsor parsor)
  }
  where
    retable dispatch = dispatch {dispatchTable = f <$> dispatchTable dispatch}

dispatching :: Dispatch b -> Value -> Either JsonError b
dispatching (Dispatch Nothing table) = \case
  v@(String t) | Just p <- Map.lookup t table -> p v
  v -> Left (JsonError [] (literals table) (Just v) JsonLiteral [])
dispatching (Dispatch (Just key) table) = \case
  v@(Object o) -> case KeyMap.lookup key o of
    Nothing -> jsonMissing ("key " <> showKey key) (Just v)
    Just (String t) | Just p <- Map.lookup t table -> p v
    Just tag ->
      Left (JsonError [Key key] (literals table) (Just tag) JsonLiteral [])
  v -> jsonMismatch "object" v

literals :: Map Text a -> [String]
literals = map show . Map.keys

orElse
  :: (Value -> Either JsonError b) -> (Value -> Either JsonError b)
  -> Value -> Either JsonError b
orElse p q v = case p v of
  Left err1 -> onFailure (jsonOrElse err1) (q v)
  success -> success

{- | `TupParsor` parses the elements of a JSON array from a position,
in every way it can, so that optional and rest elements backtrack.
A tuple of fixed length also parses its elements from known positions.
-}
data TupParsor a b = TupParsor
  { tupParsorFixed :: Maybe (Int, Vector Value -> Int -> Either JsonError b)
  , runTupParsor :: Vector Value -> Int -> [Either JsonError (b, Int)]
  }

{- | `ObjParsor` reads keys of an `Object`, ignoring other keys.
Its keys are known before parsing, so overlapping keys are found once,
as are its tags, keys which only accept string literals.
-}
data ObjParsor a b = ObjParsor
  { objParsorKeys :: [Key]
  , objParsorTags :: [(Key, Set Text)]
  , runObjParsor :: Object -> Either JsonError b
  }

instance Functor (JsonParsor a) where
  fmap f = mapParsing (fmap (onSuccess f))
instance Profunctor JsonParsor where
  dimap _ g = mapParsing (fmap (onSuccess g))
  _ #. p = coerce p
  p .# _ = coerce p
instance Choice JsonParsor where
  left' = mapParsing (fmap (fmap Left))
  right' = mapParsing (fmap (fmap Right))
instance Cochoice JsonParsor where
  unleft = mapParsing $ \p v ->
    p v >>= either pure (\_ -> jsonUnexpected (Just v))
  unright = mapParsing $ \p v ->
    p v >>= either (\_ -> jsonUnexpected (Just v)) pure
instance CocartesianMonoidal JsonParsor where
  zeroP = falseP
  p >+< q = (Left <$> coerce p) >|< (Right <$> coerce q)
instance CocartesianChoice JsonParsor
instance DisjunctiveMonoid (JsonParsor a b) where
  falseP = jsonParsor (jsonUnexpected . Just)
  p >|< q = case (jsonParsorDispatch p, jsonParsorDispatch q) of
    (Just dispatch0, Just dispatch1)
      | dispatchKey dispatch0 == dispatchKey dispatch1 ->
          let
            dispatch = Dispatch (dispatchKey dispatch0) $ Map.unionWith orElse
              (dispatchTable dispatch0) (dispatchTable dispatch1)
          in
            JsonParsor (Just dispatch) (dispatching dispatch)
    _ -> jsonParsor (orElse (runJsonParsor p) (runJsonParsor q))
instance BackusNaurForm (JsonParsor a b) where
  rule name = mapParsing (onFailure (jsonRelabel name) .)
  ruleRec name f = fix (rule name . f)
instance (x ~ (), y ~ ()) => IsString (JsonParsor x y) where
  fromString s = JsonParsor
    (Just (Dispatch Nothing (Map.singleton literal parse))) parse
    where
      literal = Text.pack s
      parse = \case
        String t | t == literal -> Right ()
        v -> Left (JsonError [] [show s] (Just v) JsonLiteral [])
instance JsonStr JsonParsor where
  jsonText = jsonParsor $ \case
    String t -> Right t
    v -> jsonMismatch "string" v
instance JsonVal JsonParsor where
  jsonNull = jsonParsor $ \case
    Null -> Right ()
    v -> jsonMismatch "null" v
  jsonBool = jsonParsor $ \case
    Bool b -> Right b
    v -> jsonMismatch "boolean" v
  jsonNumber = jsonParsor $ \case
    Number n -> Right n
    v -> jsonMismatch "number" v
  jsonValue = jsonParsor Right
  jsonArray p = jsonParsor $ \case
    Array arr -> zipWithM
      (\i v -> jsonAt (Index i) (runJsonParsor p v)) [0 ..] (Vector.toList arr)
    v -> jsonMismatch "array" v
  jsonDict key p = jsonParsor $ \case
    Object o -> for (KeyMap.toList o) $ \(k, v) -> jsonAt (Key k) $
      (,) <$> runJsonParsor key (String (Key.toText k)) <*> runJsonParsor p v
    v -> jsonMismatch "object" v
  jsonTuple tup = jsonParsor $ \case
    Array arr | Just (n, fixed) <- tupParsorFixed parsor ->
      fixed arr 0 >>= \b ->
        if n == Vector.length arr then Right b
        else jsonMissing (countElements n) (Just (Array arr))
    Array arr ->
      let
        outcomes = runTupParsor parsor arr 0
        incomplete = \case
          Left err -> err
          Right (_, n) ->
            JsonError [] [countElements n] (Just (Array arr)) JsonMissing []
      in
        case [b | Right (b, n) <- outcomes, n == Vector.length arr] of
          b : _ -> Right b
          [] -> Left (foldl jsonOrElse unexpected (map incomplete outcomes))
            where
              unexpected = JsonError [] [] (Just (Array arr)) JsonMismatch []
    v -> jsonMismatch "array" v
    where
      parsor = tup @TupParsor
  jsonObject obj = JsonParsor dispatch parse
    where
      overlap = duplicateKey (objParsorKeys obj)
      parse = \case
        Object o -> case overlap of
          Just key ->
            jsonMissing ("another key " <> showKey key) (Just (Object o))
          Nothing -> runObjParsor obj o
        v -> jsonMismatch "object" v
      dispatch = case objParsorTags obj of
        (key, tags) : _ ->
          Just (Dispatch (Just key) (Map.fromSet (const parse) tags))
        [] -> Nothing

instance Functor (TupParsor a) where
  fmap f (TupParsor fixed general) = TupParsor
    (fmap (\p arr i -> onSuccess f (p arr i)) <$> fixed)
    (\arr i -> map (fmap (first' f)) (general arr i))
instance Applicative (TupParsor a) where
  pure b = TupParsor (Just (0, \_ _ -> Right b)) (\_ i -> [Right (b, i)])
  TupParsor fixed0 general0 <*> TupParsor fixed1 general1 =
    TupParsor (liftA2 sequenced fixed0 fixed1) backtracking
    where
      sequenced (n0, p) (n1, q) = (n0 + n1, \arr i -> case p arr i of
        Left err -> Left err
        Right f -> onSuccess f (q arr $! i + n0))
      backtracking arr i = general0 arr i >>= \case
        Left err -> [Left err]
        Right (f, j) -> map (fmap (first' f)) (general1 arr j)
instance Profunctor TupParsor where
  dimap _ g = coerce . fmap g
  _ #. p = coerce p
  p .# _ = coerce p
instance Choice TupParsor where
  left' = alternate . Left
  right' = alternate . Right
instance CocartesianMonoidal TupParsor
instance CocartesianChoice TupParsor where
  alternate = either (fmap Left . coerce) (fmap Right . coerce)
instance DisjunctiveMonoid (TupParsor a b) where
  falseP = TupParsor Nothing (\_ _ -> [])
  p >|< q = TupParsor Nothing $ \arr i ->
    runTupParsor p arr i <> runTupParsor q arr i
-- | `manyP` tries longer repetitions first, never repeating an empty match.
instance Distributor TupParsor where
  manyP (TupParsor _ p) = TupParsor Nothing go
    where
      go arr i = concatMap step (p arr i) <> [Right ([], i)]
        where
          step = \case
            Left err -> [Left err]
            Right (b, j) | j > i -> map (fmap (first' (b :))) (go arr j)
            Right _ -> []
instance Alternative (TupParsor a) where
  empty = falseP
  (<|>) = (>|<)
  many = lmap repeat . manyP
  some = lmap repeat . someP
instance Alternator TupParsor
instance JsonTup JsonParsor TupParsor where
  jsonElem p = TupParsor
    (Just (1, jsonElement))
    (\arr i -> [(, i + 1) <$> jsonElement arr i])
    where
      jsonElement arr i = case arr Vector.!? i of
        Nothing ->
          jsonMissing ("at least " <> countElements (i + 1)) (Just (Array arr))
        Just v -> jsonAt (Index i) (runJsonParsor p v)

instance Functor (ObjParsor a) where
  fmap f (ObjParsor keys tags p) = ObjParsor keys tags (onSuccess f . p)
instance Applicative (ObjParsor a) where
  pure b = ObjParsor [] [] (\_ -> Right b)
  ObjParsor keys0 tags0 p0 <*> ObjParsor keys1 tags1 p1 =
    ObjParsor (keys0 <> keys1) (tags0 <> tags1) $ \o -> case p0 o of
      Left err -> Left err
      Right f -> onSuccess f (p1 o)
instance Profunctor ObjParsor where
  dimap _ g (ObjParsor keys tags p) = ObjParsor keys tags (onSuccess g . p)
  _ #. p = coerce p
  p .# _ = coerce p
instance JsonObj JsonParsor ObjParsor where
  k !: p = ObjParsor [key] tags $ \o -> case KeyMap.lookup key o of
    Nothing -> jsonMissing ("key " <> show k) (Just (Object o))
    Just v -> jsonAt (Key key) (runJsonParsor p v)
    where
      key = Key.fromText k
      tags = case jsonParsorDispatch p of
        Just (Dispatch Nothing table) -> [(key, Map.keysSet table)]
        _ -> []
  k ?: p = ObjParsor [key] [] $ \o ->
    traverse (jsonAt (Key key) . runJsonParsor p) (KeyMap.lookup key o)
    where
      key = Key.fromText k

duplicateKey :: [Key] -> Maybe Key
duplicateKey keys
  | ascending id || ascending shortlex = Nothing
  | HashSet.size (HashSet.fromList keys) == length keys = Nothing
  | otherwise = go HashSet.empty keys
  where
    ascending :: Ord b => (Key -> b) -> Bool
    ascending f = and (zipWith (\k j -> f k < f j) keys (drop 1 keys))
    shortlex key = (Text.lengthWord8 (Key.toText key), key)
    go _ [] = Nothing
    go seen (key : rest)
      | HashSet.member key seen = Just key
      | otherwise = go (HashSet.insert key seen) rest

showKey :: Key -> String
showKey = show . Key.toText

-- Printing interpreters --

-- | @aeson@'s representations of JSON strings, `Value` & `Encoding`.
class AesonStr val where
  aesonText :: Text -> val
  aesonString :: String -> val
  -- | Render a string literal, which is rendered once.
  aesonLiteral :: Text -> val
  aesonLiteral = aesonText
  -- | Render an array of a primitive at once, when that's faster.
  aesonPrimitives :: (a -> val) -> Maybe ([a] -> val)
  -- | Render an @aeson@ string `Encoding.Encoding'`.
  aesonEncodedText :: Encoding.Encoding' Text -> val
  aesonEncodedText = aesonText . encodedText

instance AesonStr Value where
  aesonText = String
  aesonString = String . Text.pack
  aesonPrimitives _ = Nothing

instance AesonStr Encoding where
  aesonText = Encoding.text
  aesonString = Encoding.string
  aesonLiteral = Encoding.unsafeToEncoding . Builder.byteString
    . LByteString.toStrict . Encoding.encodingToLazyByteString . Encoding.text
  aesonPrimitives render = Just (\as -> Encoding.list render as)
  {-# INLINE aesonPrimitives #-}
  aesonEncodedText = Encoding.unsafeToEncoding . Encoding.fromEncoding

-- | `KeyPrintor` prints the key of an `Object`, which is total.
newtype KeyPrintor a b = KeyPrintor {runKeyPrintor :: a -> Key}

instance Profunctor KeyPrintor where
  dimap f _ (KeyPrintor render) = KeyPrintor (render . f)
instance Cochoice KeyPrintor where
  unleft (KeyPrintor render) = KeyPrintor (render . Left)
  unright (KeyPrintor render) = KeyPrintor (render . Right)
instance (x ~ (), y ~ ()) => IsString (KeyPrintor x y) where
  fromString s = KeyPrintor (const key)
    where
      key = Key.fromString s
instance JsonStr KeyPrintor where
  jsonText = KeyPrintor Key.fromText
  jsonString = KeyPrintor Key.fromString

-- | @aeson@'s representations of JSON values, `Value` & `Encoding`.
class AesonStr val => AesonVal val where
  aesonNull :: val
  aesonBool :: Bool -> val
  aesonNumber :: Scientific -> val
  aesonIntegral :: Integral a => (a -> Encoding) -> a -> val
  aesonDouble :: Double -> val
  aesonList :: (a -> val) -> [a] -> val
  aesonObject :: [(Key, val)] -> val
  aesonValue :: Value -> val

instance AesonVal Value where
  aesonNull = Null
  aesonBool = Bool
  aesonNumber = Number
  aesonIntegral _ = Number . fromIntegral
  aesonDouble = Number . fromFloatDigits
  aesonList f as = Array $ Vector.create $ do
    array <- MVector.unsafeNew (length as)
    let
      write _ [] = pure array
      write i (a : rest) =
        MVector.unsafeWrite array i (f a) >> write (i + 1) rest
    write 0 as
  aesonObject = Object . KeyMap.fromList
  aesonValue = id

instance AesonVal Encoding where
  aesonNull = Encoding.null_
  aesonBool = Encoding.bool
  aesonNumber = Encoding.scientific
  aesonIntegral = id
  aesonDouble = Encoding.double
  aesonList = Encoding.list
  aesonObject = Encoding.pairs . foldMap (uncurry Encoding.pair)
  aesonValue = Encoding.value

{- | `JsonPrintor` `printorTry`s to print a value, or else `printorCheck`s it
to locate the failure. A `printorTotal` printor prints every value,
so it `printorRender`s it without trying. Totality is determined
through `rule`s, assuming those being determined are total.
A primitive `printorRenderArray`s an array of its values at once.
-}
data JsonPrintor val a b = JsonPrintor
  { printorTotal :: !(Set RuleKey -> Bool)
  , printorTry :: !(a -> Maybe val)
  , printorRender :: !(a -> val)
  , printorCheck :: !(a -> Either JsonError val)
  , printorRenderArray :: !(Maybe ([a] -> val))
  }

runJsonPrintor :: JsonPrintor val a b -> a -> Either JsonError val
runJsonPrintor p
  | printorTotal p Set.empty = Right . printorRender p
  | otherwise = \a -> maybe (printorCheck p a) Right (printorTry p a)

-- | A total `JsonPrintor`.
printing :: (a -> val) -> JsonPrintor val a b
printing render =
  JsonPrintor (const True) (Just . render) render (Right . render) Nothing

-- | A total `JsonPrintor` of a primitive.
primitive :: AesonStr val => (a -> val) -> JsonPrintor val a b
primitive render =
  (printing render) {printorRenderArray = aesonPrimitives render}
{-# INLINE primitive #-}

-- | A partial `JsonPrintor`, rendering what it tries.
trying
  :: (a -> Maybe val) -> (a -> Either JsonError val) -> JsonPrintor val a b
trying attempt check = JsonPrintor
  (const False) attempt (fromMaybe invalid . attempt) check Nothing

-- | Try each of the values, rendering them for a total printor.
tryAll
  :: Traversable f
  => (Set RuleKey -> Bool) -> (a -> Maybe b) -> (a -> b) -> f a -> Maybe (f b)
tryAll total attempt render = \as -> if isTotal
  then Just (fmap render as)
  else traverse attempt as
  where
    isTotal = total Set.empty

-- | Rendering is only ever done for a value that's printable.
invalid :: a
invalid = error "Control.Lens.Grammar.Json: rendered an unprintable value"

{- | A `rule`'s totality, assuming those being determined are total,
by induction on the values printed.
-}
ruleTotal :: RuleKey -> (Set RuleKey -> Bool) -> Set RuleKey -> Bool
ruleTotal key total rules =
  Set.member key rules || total (Set.insert key rules)

{- | `TupPrintor` prints the elements of a JSON array,
counted to locate a failure of a later element.
-}
data TupPrintor val a b = TupPrintor
  { tupPrintorTotal :: !(Set RuleKey -> Bool)
  , tupPrintorTry :: !(a -> Maybe (DList val))
  , tupPrintorRender :: !(a -> [val] -> [val])
  , tupPrintorCheck :: !(a -> Elements val)
  }

-- | Printed elements, counted to locate a failure of a later element.
newtype Elements val = Elements (Either JsonError (Int, DList val))
instance Semigroup (Elements val) where
  Elements (Right (count0, elements0)) <> Elements later = Elements $
    case later of
      Right (count1, elements1) ->
        Right (count0 + count1, elements0 <> elements1)
      Left err -> Left (shiftIndex count0 err)
  failure <> _ = failure
instance Monoid (Elements val) where
  mempty = Elements (Right (0, mempty))

shiftIndex :: Int -> JsonError -> JsonError
shiftIndex count err = case jsonErrorPath err of
  Index i : path -> err {jsonErrorPath = Index (i + count) : path}
  _ -> err

{- | `ObjPrintor` writes keys of an `Object`.
Its keys are known before printing, so overlapping keys are found once.
-}
data ObjPrintor val a b = ObjPrintor
  { objPrintorKeys :: [Key]
  , objPrintorTotal :: !(Set RuleKey -> Bool)
  , objPrintorTry :: !(a -> Maybe (DList (Key, val)))
  , objPrintorRender :: !(a -> [(Key, val)] -> [(Key, val)])
  , objPrintorCheck :: !(a -> Either JsonError [(Key, val)])
  }

printObject :: AesonVal val => [(Key, val)] -> Either JsonError val
printObject props = case duplicateKey (map fst props) of
  Just key -> printDuplicate key
  Nothing -> Right (aesonObject props)

printDuplicate :: Key -> Either JsonError a
printDuplicate key = jsonMissing ("key " <> showKey key <> " twice") Nothing

instance Functor (JsonPrintor val a) where
  fmap _ (JsonPrintor total attempt render check renderArray) =
    JsonPrintor total attempt render check renderArray
instance Profunctor (JsonPrintor val) where
  dimap f _ (JsonPrintor total attempt render check renderArray) =
    JsonPrintor total (attempt . f) (\a -> render $! f a) (check . f)
      (fmap (. map f) renderArray)
  _ #. p = coerce p
  p .# _ = coerce p
instance Cochoice (JsonPrintor val) where
  unleft (JsonPrintor total attempt render check renderArray) =
    JsonPrintor total (attempt . Left) (render . Left) (check . Left)
      (fmap (. map Left) renderArray)
  unright (JsonPrintor total attempt render check renderArray) =
    JsonPrintor total (attempt . Right) (render . Right) (check . Right)
      (fmap (. map Right) renderArray)
instance CocartesianMonoidal (JsonPrintor val) where
  zeroP = JsonPrintor (const True) absurd absurd absurd Nothing
  p >+< q = JsonPrintor
    (\rules -> printorTotal p rules && printorTotal q rules)
    (either (printorTry p) (printorTry q))
    (either (printorRender p) (printorRender q))
    (either (printorCheck p) (printorCheck q))
    Nothing
instance Choice (JsonPrintor val) where
  left' p = trying
    (either (printorTry p) (const Nothing))
    (either (printorCheck p) (\_ -> jsonUnexpected Nothing))
  right' p = trying
    (either (const Nothing) (printorTry p))
    (either (\_ -> jsonUnexpected Nothing) (printorCheck p))
instance CocartesianChoice (JsonPrintor val)
instance DisjunctiveMonoid (JsonPrintor val a b) where
  falseP = trying (const Nothing) (\_ -> jsonUnexpected Nothing)
  p >|< q = JsonPrintor
    (\rules -> printorTotal p rules || printorTotal q rules)
    (\a -> printorTry p a <|> printorTry q a)
    (\a -> fromMaybe (printorRender q a) (printorTry p a))
    (\a -> case printorCheck p a of
      Left err1 -> onFailure (jsonOrElse err1) (printorCheck q a)
      success -> success)
    Nothing
instance BackusNaurForm (JsonPrintor val a b) where
  rule name = ruleP (NamedRule name) name
  ruleRec name f = fix (rule name . f)

-- | A `rule` with a key, labelling its failures with a name.
ruleP :: RuleKey -> String -> JsonPrintor val a b -> JsonPrintor val a b
ruleP key name p = p
  { printorTotal = ruleTotal key (printorTotal p)
  , printorCheck = onFailure (jsonRelabel name) . printorCheck p
  }

instance (AesonStr val, x ~ (), y ~ ()) => IsString (JsonPrintor val x y) where
  fromString s = printing (const literal)
    where
      literal = aesonLiteral (Text.pack s)
instance AesonStr val => JsonStr (JsonPrintor val) where
  jsonText = primitive aesonText
  jsonString = primitive aesonString
  jsonEncodedText encoding = withPrism encoding $ \encode _ ->
    primitive (aesonEncodedText . encode)
instance AesonVal val => JsonVal (JsonPrintor val) where
  jsonNull = primitive (const aesonNull)
  jsonBool = primitive aesonBool
  jsonNumber = primitive aesonNumber
  jsonInt = primitive (aesonIntegral Encoding.int)
  jsonInt8 = primitive (aesonIntegral Encoding.int8)
  jsonInt16 = primitive (aesonIntegral Encoding.int16)
  jsonInt32 = primitive (aesonIntegral Encoding.int32)
  jsonInt64 = primitive (aesonIntegral Encoding.int64)
  jsonWord = primitive (aesonIntegral Encoding.word)
  jsonWord8 = primitive (aesonIntegral Encoding.word8)
  jsonWord16 = primitive (aesonIntegral Encoding.word16)
  jsonWord32 = primitive (aesonIntegral Encoding.word32)
  jsonWord64 = primitive (aesonIntegral Encoding.word64)
  jsonDouble = primitive aesonDouble
  jsonValue = printing aesonValue
  jsonArray p = JsonPrintor
    (\rules -> printorTotal p rules)
    (\as -> if printorTotal p Set.empty
      then Just (render as)
      else aesonList id <$> traverse (printorTry p) as)
    render
    (\as -> aesonList id <$>
      zipWithM (\i a -> jsonAt (Index i) (printorCheck p a)) [0 ..] as)
    Nothing
    where
      render = fromMaybe (aesonList (printorRender p)) (printorRenderArray p)
  jsonDict key p = trying attempt check
    where
      keyOf = runKeyPrintor key
      property (a, c) = (keyOf a, printorRender p c)
      tryProperty (a, c) = (keyOf a,) <$> printorTry p c
      tryProperties = tryAll (printorTotal p) tryProperty property
      attempt entries = do
        props <- tryProperties entries
        guard (isNothing (duplicateKey (map fst props)))
        Just (aesonObject props)
      check = traverse entry >=> printObject
      entry (a, c) = (k,) <$> jsonAt (Key k) (printorCheck p c)
        where
          k = keyOf a
  jsonTuple tup = JsonPrintor
    (\rules -> tupPrintorTotal tup rules)
    (fmap (aesonList id . toList) . tupPrintorTry tup)
    (\a -> aesonList id (tupPrintorRender tup a []))
    (\a -> case tupPrintorCheck tup a of
      Elements printed -> aesonList id . toList . snd <$> printed)
    Nothing
  jsonObject obj = case duplicateKey (objPrintorKeys printor) of
    Just key -> trying (const Nothing) (\_ -> printDuplicate key)
    Nothing -> JsonPrintor
      (\rules -> objPrintorTotal printor rules)
      (fmap (aesonObject . toList) . objPrintorTry printor)
      (\a -> aesonObject (objPrintorRender printor a []))
      (fmap aesonObject . objPrintorCheck printor)
      Nothing
    where
      printor = obj @(ObjPrintor val)
  jsonTyped :: forall a. Typeable a
    => JsonPrintor val a a -> JsonPrintor val a a
  jsonTyped = ruleP (TypedRule (SomeTypeRep rep)) (show rep)
    where
      rep = typeRep @a

instance Functor (TupPrintor val a) where
  fmap _ (TupPrintor total attempt render check) =
    TupPrintor total attempt render check
instance Applicative (TupPrintor val a) where
  pure _ =
    TupPrintor (const True) (const (Just mempty)) (\_ rest -> rest) mempty
  p <*> q = TupPrintor
    (\rules -> tupPrintorTotal p rules && tupPrintorTotal q rules)
    (\a -> (<>) <$> tupPrintorTry p a <*> tupPrintorTry q a)
    (\a rest -> tupPrintorRender p a $! tupPrintorRender q a rest)
    (tupPrintorCheck p <> tupPrintorCheck q)
instance Profunctor (TupPrintor val) where
  dimap f _ (TupPrintor total attempt render check) =
    TupPrintor total (attempt . f)
      (\a rest -> let b = f a in b `seq` render b rest) (check . f)
  _ #. p = coerce p
  p .# _ = coerce p
instance CocartesianMonoidal (TupPrintor val) where
  zeroP = TupPrintor (const True) absurd absurd absurd
  p >+< q = TupPrintor
    (\rules -> tupPrintorTotal p rules && tupPrintorTotal q rules)
    (either (tupPrintorTry p) (tupPrintorTry q))
    (\e rest -> case e of
      Left a -> tupPrintorRender p a rest
      Right b -> tupPrintorRender q b rest)
    (either (tupPrintorCheck p) (tupPrintorCheck q))
instance Distributor (TupPrintor val) where
  manyP p = TupPrintor
    (\rules -> tupPrintorTotal p rules)
    (fmap mconcat . tryAll (tupPrintorTotal p) (tupPrintorTry p)
      (\a -> DList.fromList (tupPrintorRender p a [])))
    (\as rest -> foldr (\a printed -> tupPrintorRender p a $! printed) rest as)
    (foldMap (tupPrintorCheck p))
  optionalP p = TupPrintor
    (\rules -> tupPrintorTotal p rules)
    (maybe (Just mempty) (tupPrintorTry p))
    (\ma rest -> maybe rest (\a -> tupPrintorRender p a rest) ma)
    (foldMap (tupPrintorCheck p))
-- | `optionP` omits its default.
instance Alternative (TupPrintor val a) where
  empty = falseP
  (<|>) = (>|<)
  many = lmap repeat . manyP
  some = lmap repeat . someP
instance Alternator (TupPrintor val) where
  optionP def p = pureP def >|< p
instance Choice (TupPrintor val) where
  left' = alternate . Left
  right' = alternate . Right
unprintable :: Elements val
unprintable = Elements (jsonUnexpected Nothing)

-- | A partial `TupPrintor`, rendering what it tries.
tupTrying
  :: (a -> Maybe (DList val)) -> (a -> Elements val) -> TupPrintor val a b
tupTrying attempt =
  TupPrintor (const False) attempt
    (\a -> DList.apply (fromMaybe invalid (attempt a)))

instance CocartesianChoice (TupPrintor val) where
  alternate = \case
    Left p -> tupTrying
      (either (tupPrintorTry p) (const Nothing))
      (either (tupPrintorCheck p) (\_ -> unprintable))
    Right p -> tupTrying
      (either (const Nothing) (tupPrintorTry p))
      (either (\_ -> unprintable) (tupPrintorCheck p))
instance DisjunctiveMonoid (TupPrintor val a b) where
  falseP = tupTrying (const Nothing) (\_ -> unprintable)
  p >|< q = TupPrintor
    (\rules -> tupPrintorTotal p rules || tupPrintorTotal q rules)
    (\a -> tupPrintorTry p a <|> tupPrintorTry q a)
    (\a rest -> maybe
      (tupPrintorRender q a rest) (`DList.apply` rest) (tupPrintorTry p a))
    (\a -> case (tupPrintorCheck p a, tupPrintorCheck q a) of
      (Elements (Left err0), Elements (Left err1)) ->
        Elements (Left (jsonOrElse err0 err1))
      (Elements (Left _), printed) -> printed
      (printed, _) -> printed)

instance AesonVal val => JsonTup (JsonPrintor val) (TupPrintor val) where
  jsonElem p = TupPrintor
    (\rules -> printorTotal p rules)
    (fmap DList.singleton . printorTry p)
    (\a rest -> let printed = printorRender p a in printed `seq` printed : rest)
    (\a -> Elements $ (\printed -> (1, pure printed))
      <$> jsonAt (Index 0) (printorCheck p a))

instance Functor (ObjPrintor val a) where
  fmap _ (ObjPrintor keys total attempt render check) =
    ObjPrintor keys total attempt render check
instance Applicative (ObjPrintor val a) where
  pure _ =
    ObjPrintor [] (const True) (const (Just mempty)) (\_ rest -> rest)
      (\_ -> Right [])
  ObjPrintor keys0 total0 try0 render0 check0
    <*> ObjPrintor keys1 total1 try1 render1 check1 = ObjPrintor
      (keys0 <> keys1)
      (\rules -> total0 rules && total1 rules)
      (\a -> (<>) <$> try0 a <*> try1 a)
      (\a rest -> render0 a $! render1 a rest)
      (\a -> (<>) <$> check0 a <*> check1 a)
instance Profunctor (ObjPrintor val) where
  dimap f _ (ObjPrintor keys total attempt render check) =
    ObjPrintor keys total
      (attempt . f) (\a rest -> let b = f a in b `seq` render b rest)
      (check . f)
  _ #. p = coerce p
  p .# _ = coerce p
instance AesonVal val => JsonObj (JsonPrintor val) (ObjPrintor val) where
  k !: p = ObjPrintor [key]
    (\rules -> printorTotal p rules)
    (fmap property . printorTry p)
    (\a rest -> (key, printorRender p a) : rest)
    (printProperty key p)
    where
      key = Key.fromText k
      property printed = DList.singleton (key, printed)
  k ?: p = ObjPrintor [key]
    (\rules -> printorTotal p rules)
    (maybe (Just mempty) (fmap property . printorTry p))
    (\ma rest -> maybe rest (\a -> (key, printorRender p a) : rest) ma)
    (maybe (Right []) (printProperty key p))
    where
      key = Key.fromText k
      property printed = DList.singleton (key, printed)

printProperty
  :: Key -> JsonPrintor val a b -> a -> Either JsonError [(Key, val)]
printProperty key p a =
  (\printed -> [(key, printed)]) <$> jsonAt (Key key) (printorCheck p a)

-- TypeScript interpreters --

data TsType
  = TsAlias String -- ^ @T@, a reference to a type alias
  | TsNull -- ^ @null@
  | TsBoolean -- ^ @boolean@
  | TsNumber -- ^ @number@
  | TsString -- ^ @string@
  | TsLiteral Text -- ^ @"abc"@
  | TsArray TsType -- ^ @T[]@
  | TsDict TsType -- ^ @{[key: string]: T}@
  | TsTuple [TsElement] -- ^ @[T, U?, ...V[]]@
  | TsObject [TsProperty] -- ^ @{abc: T, xyz?: U}@
  | TsUnion [TsType] -- ^ @T | U@, or @never@ when empty
  deriving stock (Eq, Ord)

data TsElement
  = TsRequired TsType -- ^ @T@
  | TsOptional TsType -- ^ @T?@
  | TsRest TsType -- ^ @...T[]@
  deriving stock (Eq, Ord)

-- | A property of a TypeScript object type, @abc: T@ or @abc?: T@.
data TsProperty = TsProperty Text Bool TsType
  deriving stock (Eq, Ord)

newtype TsGrammor a b = TsGrammor (TsDefining TsType)

newtype TsTupGrammor a b = TsTupGrammor
  {runTsTupGrammor :: Ap TsDefining TsShapes}

newtype TsObjGrammor a b = TsObjGrammor
  {runTsObjGrammor :: Ap TsDefining [TsProperty]}

{- | Defining TypeScript types, reading the rules being defined which are
unguarded by an array, object or tuple, each noting whether it's been
unrolled, and updating the named rules & their definitions.
-}
type TsDefining = ReaderT (Map RuleKey Bool) (State TsDefinitions)

data TsDefinitions = TsDefinitions
  { tsRuleNames :: Map RuleKey String
  , tsRules :: Map String TsType
  }

data RuleKey = NamedRule String | TypedRule SomeTypeRep
  deriving stock (Eq, Ord)

{- | Define a rule once, under the first of its names which isn't taken,
so that every other occurrence of it, recursive or not, is its name.
Its name is reserved, as `never`, while its definition is built.
An unguarded occurrence is its least fixpoint instead, unrolled once,
so that a rule of a rule is the rule, and a rule recurring unguarded
contributes `never`, since JSON values are finite.
-}
tsDefine :: RuleKey -> [String] -> TsGrammor a b -> TsGrammor c d
tsDefine key names (TsGrammor body) = TsGrammor $ do
  unguarded <- ask
  defs <- lift get
  case (Map.lookup key unguarded, Map.lookup key (tsRuleNames defs)) of
    (Just True, _) -> pure (tsUnion [])
    (Just False, _) -> local (Map.insert key True) body
    (Nothing, Just name) -> pure (TsAlias name)
    (Nothing, Nothing) -> do
      let name = freshName (tsRules defs) names
      lift $ put defs
        { tsRuleNames = Map.insert key name (tsRuleNames defs)
        , tsRules = Map.insert name (tsUnion []) (tsRules defs)
        }
      definition <- local (Map.insert key False) body
      lift $ modify $ \defined ->
        defined {tsRules = Map.insert name definition (tsRules defined)}
      pure (TsAlias name)

tsGuarded :: TsDefining a -> TsDefining a
tsGuarded = local (const Map.empty)

freshName :: Map String a -> [String] -> String
freshName taken names = fromMaybe primed (find (`Map.notMember` taken) names)
  where
    primed = until (`Map.notMember` taken) (<> "'") (last names)

qualifiedTypeName :: SomeTypeRep -> String
qualifiedTypeName (SomeTypeRep rep) =
  unwords (constructor : map typeArgument args)
  where
    (tyCon, args) = splitApps rep
    constructor = tyConModule tyCon <> "." <> tyConName tyCon
    typeArgument arg@(SomeTypeRep argRep) = case splitApps argRep of
      (_, []) -> qualifiedTypeName arg
      _ -> "(" <> qualifiedTypeName arg <> ")"

tsType :: TsType -> TsGrammor a b
tsType = TsGrammor . pure

tsUnion :: [TsType] -> TsType
tsUnion types = case nub (concatMap alternatives types) of
  [t] -> t
  ts -> TsUnion ts
  where
    alternatives = \case
      TsUnion ts -> ts
      t -> [t]

tsObject :: [TsProperty] -> TsType
tsObject props
  | length (nub names) == length names = TsObject props
  | otherwise = tsUnion []
  where
    names = [name | TsProperty name _ _ <- props]

{- | Alternative shapes of a TypeScript tuple type,
so that `>*<` concatenates each pair of shapes and `>+<` unites them.
-}
type TsShapes = Ap [] [TsElement]

tsElementType :: TsElement -> TsType
tsElementType = \case
  TsRequired t -> t
  TsOptional t -> t
  TsRest t -> t

{- | The union of tuple types of some shapes. TypeScript requires that
a tuple type has at most one rest element, no optional element after
a rest element, and no required element after an optional element.
So, the elements from the first rest element to the last are merged
into one rest element, and optional elements are expanded into
alternative shapes wherever they'd be followed by a required or
rest element, or a rest element precedes them.
Then, alternative shapes are merged exactly, where they differ by
one required or optional element's type, into a union, or by one more
element, into an optional or rest element, so that @[A] | [B]@ is @[A | B]@,
@[A] | [A, B]@ is @[A, B?]@ & @[] | [A, ...A[]]@ is @[...A[]]@.
-}
tsTuple :: TsShapes -> TsType
tsTuple (Ap shapes) = tsUnion $ TsTuple <$>
  merged (nub (concatMap (expand False . mergeRests) shapes))
  where
    merged alternatives =
      case [ (i, j, shape)
           | merge <- [unioned, extended]
           , (i, a) <- zip [0 :: Int ..] alternatives
           , (j, b) <- zip [0 ..] alternatives
           , i /= j
           , Just shape <- [merge a b]
           ] of
        (i, j, shape) : _ -> merged
          [ if k == min i j then shape else alternative
          | (k, alternative) <- zip [0 ..] alternatives, k /= max i j ]
        [] -> alternatives
    unioned a b = case break (uncurry (/=)) (zip a b) of
      (same, (x, y) : others)
        | length a == length b, all (uncurry (==)) others
        , Just el <- unionedElement x y ->
            Just (map fst same <> [el] <> map fst others)
      _ -> Nothing
    unionedElement x y = case (x, y) of
      (TsRequired s, TsRequired t) -> Just (TsRequired (tsUnion [s, t]))
      (TsOptional s, TsOptional t) -> Just (TsOptional (tsUnion [s, t]))
      _ -> Nothing
    extended a b
      | any isRest a = Nothing
      | otherwise = stripPrefix a b >>= \case
          [TsRequired t] -> Just (a <> [TsOptional t])
          [TsOptional _] -> Just b
          [TsRest _] -> Just b
          [TsRequired t, TsRest u] | t == u -> Just (a <> [TsRest t])
          _ -> Nothing
    isRest = \case TsRest _ -> True; _ -> False
    mergeRests els = case findIndices isRest els of
      start : rests@(_ : _) ->
        let
          (before, others) = splitAt start els
          (middle, after) = splitAt (last rests - start + 1) others
        in
          before <> [TsRest (tsUnion (map tsElementType middle))] <> after
      _ -> els
    expand _ [] = [[]]
    expand restBefore (el : els) = case el of
      TsOptional t | restBefore || not (optionalTail els) ->
        expand restBefore els <> map (TsRequired t :) (expand restBefore els)
      TsRest _ -> map (el :) (expand True els)
      _ -> map (el :) (expand restBefore els)
    optionalTail = \case
      [] -> True
      [TsRest _] -> True
      TsOptional _ : els -> optionalTail els
      _ -> False

deriving via Grammor (TsDefining TsType) a
  instance Functor (TsGrammor a)
deriving via Grammor (TsDefining TsType)
  instance Profunctor TsGrammor
deriving via Grammor (TsDefining TsType)
  instance Choice TsGrammor
instance Cochoice TsGrammor where
  unleft = coerce
  unright = coerce
instance CocartesianMonoidal TsGrammor
instance CocartesianChoice TsGrammor where
  alternate = either coerce coerce
instance DisjunctiveMonoid (TsGrammor a b) where
  falseP = tsType (tsUnion [])
  TsGrammor t0 >|< TsGrammor t1 =
    TsGrammor (liftA2 (\a b -> tsUnion [a, b]) t0 t1)
instance BackusNaurForm (TsGrammor a b) where
  rule name = tsDefine (NamedRule name) [name]
  ruleRec name f = rule name (f self)
    where
      self = tsDefine (NamedRule name) [name] falseP
instance (x ~ (), y ~ ()) => IsString (TsGrammor x y) where
  fromString = tsType . TsLiteral . Text.pack
instance JsonStr TsGrammor where
  jsonText = tsType TsString
instance JsonVal TsGrammor where
  jsonNull = tsType TsNull
  jsonBool = tsType TsBoolean
  jsonNumber = tsType TsNumber
  jsonArray (TsGrammor t) = TsGrammor (TsArray <$> tsGuarded t)
  jsonDict _ (TsGrammor t) = TsGrammor (TsDict <$> tsGuarded t)
  jsonTuple tup = TsGrammor (tsTuple <$> getAp (runTsTupGrammor tup))
  jsonObject obj = TsGrammor (tsObject <$> getAp (runTsObjGrammor obj))
  jsonTyped :: forall a. Typeable a => TsGrammor a a -> TsGrammor a a
  jsonTyped = tsDefine (TypedRule rep) [show rep, qualifiedTypeName rep]
    where
      rep = SomeTypeRep (typeRep @a)

deriving via Grammor (Ap TsDefining TsShapes) a
  instance Functor (TsTupGrammor a)
deriving via Grammor (Ap TsDefining TsShapes) a
  instance Applicative (TsTupGrammor a)
deriving via Grammor (Ap TsDefining TsShapes)
  instance Profunctor TsTupGrammor
instance CocartesianMonoidal TsTupGrammor
instance Choice TsTupGrammor where
  left' = coerce
  right' = coerce
instance CocartesianChoice TsTupGrammor where
  alternate = either coerce coerce
instance DisjunctiveMonoid (TsTupGrammor a b) where
  falseP = TsTupGrammor (pure (Ap []))
  TsTupGrammor s0 >|< TsTupGrammor s1 = TsTupGrammor (liftA2 unite s0 s1)
    where
      unite (Ap shapes0) (Ap shapes1) = Ap (shapes0 <> shapes1)
-- | `manyP` is a rest element, of the union of the elements of its shapes.
instance Distributor TsTupGrammor where
  manyP (TsTupGrammor s) = TsTupGrammor (rest <$> s)
    where
      rest (Ap shapes) = Ap $
        case concatMap (map tsElementType) shapes of
          [] -> [[]]
          ts -> [[TsRest (tsUnion ts)]]
instance Alternative (TsTupGrammor a) where
  empty = falseP
  (<|>) = (>|<)
  many = lmap repeat . manyP
  some = lmap repeat . someP
instance Alternator TsTupGrammor
instance JsonTup TsGrammor TsTupGrammor where
  jsonElem (TsGrammor t) =
    TsTupGrammor (Ap ((\ty -> Ap [[TsRequired ty]]) <$> tsGuarded t))

deriving via Grammor (Ap TsDefining [TsProperty]) a
  instance Functor (TsObjGrammor a)
deriving via Grammor (Ap TsDefining [TsProperty]) a
  instance Applicative (TsObjGrammor a)
deriving via Grammor (Ap TsDefining [TsProperty])
  instance Profunctor TsObjGrammor
instance JsonObj TsGrammor TsObjGrammor where
  k !: TsGrammor t =
    TsObjGrammor (Ap (pure . TsProperty k False <$> tsGuarded t))
  k ?: TsGrammor t =
    TsObjGrammor (Ap (pure . TsProperty k True <$> tsGuarded t))

-- Rendering TypeScript --

-- | Render the TypeScript type alias declarations of rules, sharing them.
renderTypeScript :: [TsGrammor () ()] -> Text
renderTypeScript roots =
  Text.unlines (map declaration (Map.toList (tsRules definitions)))
  where
    definitions = execState
      (runReaderT (traverse_ (\(TsGrammor ts) -> ts) roots) Map.empty)
      (TsDefinitions Map.empty Map.empty)
    declaration (name, ty) =
      "export type " <> tsIdentifier name <> " = " <> renderTsType ty <> ";"

renderTsType :: TsType -> Text
renderTsType = \case
  TsAlias name -> tsIdentifier name
  TsNull -> "null"
  TsBoolean -> "boolean"
  TsNumber -> "number"
  TsString -> "string"
  TsLiteral t -> tsStringLiteral t
  TsArray t -> renderTsOperand t <> "[]"
  TsDict t -> "{ [key: string]: " <> renderTsType t <> " }"
  TsTuple els -> "[" <> Text.intercalate ", " (map renderTsElement els) <> "]"
  TsObject [] -> "{}"
  TsObject props ->
    "{ " <> Text.intercalate "; " (map renderTsProperty props) <> " }"
  TsUnion [] -> "never"
  TsUnion ts -> Text.intercalate " | " (map renderTsType ts)

renderTsOperand :: TsType -> Text
renderTsOperand = \case
  TsUnion ts@(_ : _ : _) -> "(" <> renderTsType (TsUnion ts) <> ")"
  t -> renderTsType t

renderTsElement :: TsElement -> Text
renderTsElement = \case
  TsRequired t -> renderTsType t
  TsOptional t -> renderTsOperand t <> "?"
  TsRest t -> "..." <> renderTsOperand t <> "[]"

renderTsProperty :: TsProperty -> Text
renderTsProperty (TsProperty name isOptional t) =
  tsPropertyKey name <> (if isOptional then "?: " else ": ") <> renderTsType t

tsPropertyKey :: Text -> Text
tsPropertyKey name
  | isIdentifier name = name
  | otherwise = tsStringLiteral name
  where
    isIdentifier t = case Text.uncons t of
      Just (c, rest) -> identifierStart c && Text.all identifierChar rest
      Nothing -> False
    identifierStart c = isAlpha c || c == '_' || c == '$'
    identifierChar c = isAlphaNum c || c == '_' || c == '$'

tsStringLiteral :: Text -> Text
tsStringLiteral = LText.toStrict . encodeToLazyText . String

-- | A TypeScript identifier for a rule name, like @Box_List_Int@.
tsIdentifier :: String -> Text
tsIdentifier name = case Text.uncons ident of
  Nothing -> "T"
  Just (c, _) | isDigit c -> "T_" <> ident
  _ -> ident
  where
    ident = Text.intercalate "_"
      [part | part <- Text.split (not . isAlphaNum) (Text.pack spelled)
      , not (Text.null part)]
    spelled = concatMap (\c -> if c == '[' then " List " else [c]) name

-- Json instance helpers

-- | An enumeration of strings, which a map's key may be.
jsonEnumWith :: JsonStr p => (a -> Text) -> [a] -> p a a
jsonEnumWith f as = prism' f (\t -> lookup t [(f a, a) | a <- as]) ?< jsonText

-- | An enumeration of string literals, typed as their union.
jsonEnum :: (Eq a, JsonVal p) => (a -> Text) -> [a] -> p a a
jsonEnum f as = orP [only a >? fromString (Text.unpack (f a)) | a <- as]

jsonTag :: JsonVal p => Text -> p a b -> p a b
jsonTag k p = jsonObject (k !: p)

boundedScientific :: Scientific -> Maybe Scientific
boundedScientific s = s <$ guard (abs (base10Exponent s) <= 1024)

_BoundedInteger :: (Integral a, Bounded a) => Prism' Scientific a
_BoundedInteger = prism' fromIntegral toBoundedInteger

jsonBoundedInteger :: (Integral a, Bounded a, JsonVal p) => p a a
jsonBoundedInteger = _BoundedInteger ?< jsonNumber

jsonRealFloat :: (RealFloat a, JsonVal p) => p a a -> p a a
jsonRealFloat finite = dimap finiteness (either id id) (finite >+< nonFinite)
  where
    finiteness x = if isNaN x || isInfinite x then Right x else Left x
    nonFinite = dimap sign value (jsonNull >+< "+inf" >+< "-inf")
    sign x
      | isNaN x = Left ()
      | x > 0 = Right (Left ())
      | otherwise = Right (Right ())
    value = either (\_ -> 0/0) (either (\_ -> 1/0) (\_ -> negate 1/0))

_RealFrac :: (Fractional a, Real a) => Prism' Scientific a
_RealFrac = prism' realToFrac (fmap realToFrac . boundedScientific)

jsonRealFrac :: (Fractional a, Real a, JsonVal p) => p a a
jsonRealFrac = _RealFrac ?< jsonNumber

-- | A time, encoded as @aeson@ encodes it.
encodedTime
  :: (a -> Encoding.Encoding' Text) -> (Text -> Either String a)
  -> Prism Text (Encoding.Encoding' Text) a a
encodedTime f g =
  prism f (\t -> either (\_ -> Left (Encoding.text t)) Right (g t))

_Day :: Prism Text (Encoding.Encoding' Text) Day Day
_Day = encodedTime Encoding.day TimeText.parseDay

_Month :: Prism Text (Encoding.Encoding' Text) Month Month
_Month = encodedTime Encoding.month TimeText.parseMonth

_Quarter :: Prism Text (Encoding.Encoding' Text) Quarter Quarter
_Quarter = encodedTime Encoding.quarter TimeText.parseQuarter

_TimeOfDay :: Prism Text (Encoding.Encoding' Text) TimeOfDay TimeOfDay
_TimeOfDay = encodedTime Encoding.timeOfDay TimeText.parseTimeOfDay

_LocalTime :: Prism Text (Encoding.Encoding' Text) LocalTime LocalTime
_LocalTime = encodedTime Encoding.localTime TimeText.parseLocalTime

_ZonedTime :: Prism Text (Encoding.Encoding' Text) ZonedTime ZonedTime
_ZonedTime = encodedTime Encoding.zonedTime TimeText.parseZonedTime

_UTCTime :: Prism Text (Encoding.Encoding' Text) UTCTime UTCTime
_UTCTime = encodedTime Encoding.utcTime TimeText.parseUTCTime

-- | The text of an @aeson@ string `Encoding.Encoding'`.
encodedText :: Encoding.Encoding' Text -> Text
encodedText = Text.dropAround (== '"') . Text.decodeLatin1
  . LByteString.toStrict . Encoding.encodingToLazyByteString

jsonChar :: JsonStr p => p Char Char
jsonChar = prism' Text.singleton single ?< jsonText
  where
    single t = case Text.uncons t of
      Just (c, rest) | Text.null rest -> Just c
      _ -> Nothing

jsonKey :: JsonStr p => p Key Key
jsonKey = iso Key.toText Key.fromText >~ jsonText

jsonVersion :: JsonStr p => p Version Version
jsonVersion = prism' (Text.pack . showVersion) version ?< jsonText
  where
    version t =
      listToMaybe [v | (v, "") <- readP_to_S parseVersion (Text.unpack t)]

jsonUUID :: JsonStr p => p UUID UUID
jsonUUID = prism' UUID.toText UUID.fromText ?< jsonText

jsonURI :: JsonStr p => p URI URI
jsonURI = prism'
  (\uri -> Text.pack (URI.uriToString id uri ""))
  (URI.parseURI . Text.unpack)
  ?< jsonText

-- | Days of the week, named as @aeson@ names them.
weekdays :: ((DayOfWeek -> Text) -> [DayOfWeek] -> r) -> r
weekdays enumerate = enumerate (Text.toLower . Text.pack . show)
  [Monday, Tuesday, Wednesday, Thursday, Friday, Saturday, Sunday]

-- | Quarters of the year, named as @aeson@ names them.
quarters :: ((QuarterOfYear -> Text) -> [QuarterOfYear] -> r) -> r
quarters enumerate =
  enumerate (Text.toLower . Text.pack . show) [Q1, Q2, Q3, Q4]

-- | Read a `Scientific`, quickly when it's a canonical integer.
readScientific :: Text -> Maybe Scientific
readScientific t
  | canonical, Right (i, _) <- TextRead.signed TextRead.decimal t =
      Just (fromInteger i)
  | otherwise = readMaybe (Text.unpack t)
  where
    digits = fromMaybe t (Text.stripPrefix "-" t)
    canonical = not (Text.null digits) && Text.all isDigit digits
      && (Text.length digits == 1 || Text.take 1 digits /= "0")

-- | `Scientific` map keys, as @aeson@ renders them.
jsonScientificKey :: JsonStr p => p Scientific Scientific
jsonScientificKey = prism' render readScientific ?< jsonText
  where
    render s
      | e < 0 || e > 1024 = Text.pack (formatScientific Generic Nothing s)
      | otherwise = Text.pack (show (coefficient s * 10 ^ e))
      where
        e = base10Exponent s

-- | Integral map keys, as @aeson@ renders them.
jsonIntKey :: (Show a, JsonStr p) => APrism' Scientific a -> p a a
jsonIntKey integral = prism'
  (Text.pack . show) (readScientific >=> preview (clonePrism integral))
  ?< jsonText

-- | `RealFloat` map keys, as @aeson@ renders them.
jsonRealFloatKey :: (RealFloat a, Show a, JsonStr p) => p a a
jsonRealFloatKey = prism' render parse ?< jsonText
  where
    render d
      | isInfinite d = if d > 0 then "+inf" else "-inf"
      | otherwise = Text.pack (show d)
    parse = \case
      "NaN" -> Just (0/0)
      "+inf" -> Just (1/0)
      "-inf" -> Just (negate 1/0)
      t -> toRealFloat <$> readScientific t

keysCoerced :: Coercible k j => Iso' [(k, v)] [(j, v)]
keysCoerced = iso (map (first' coerce)) (map (first' coerce))

-- Json instances

makePrisms ''These

-- base
instance Json Bool where
  json = jsonBool
  jsonKeyMap = jsonDict
    (jsonEnumWith (\b -> if b then "true" else "false") [False, True]) json
instance Json Ordering where
  json = jsonTyped (jsonEnum (Text.pack . show) [LT, EQ, GT])
instance Json () where json = jsonTuple oneP
instance Json Void where
  json = zeroP
  jsonKeyMap = jsonDict (prism' absurd (const Nothing) ?< jsonText) json
instance Json Char where
  json = jsonTyped jsonChar
  jsonList = jsonString
  jsonKeyMap = jsonDict jsonChar json
  jsonKeyListMap = jsonDict jsonString json
instance Json a => Json [a] where
  json = jsonList
  jsonKeyMap = jsonKeyListMap @a
instance Json a => Json (Maybe a) where
  json = eotMaybe . swapped >~ jsonNull >+< json
instance (Json a, Json b) => Json (Either a b) where
  json = jsonTag "Left" json >+< jsonTag "Right" json
instance Json Double where
  json = jsonTyped (jsonRealFloat jsonDouble)
  jsonKeyMap = jsonDict jsonRealFloatKey json
instance Json Float where
  json = jsonTyped $
    jsonRealFloat (iso fromFloatDigits toRealFloat >~ jsonNumber)
  jsonKeyMap = jsonDict jsonRealFloatKey json
instance (Integral a, Json a) => Json (Ratio a) where
  json = prism'
    (\r -> (numerator r, denominator r))
    (\(n, d) -> n % d <$ guard (d /= 0))
    ?< jsonObject ("numerator" !: json >*< "denominator" !: json)
instance HasResolution a => Json (Fixed a) where
  json = jsonRealFrac
  jsonKeyMap = jsonDict (iso realToFrac realToFrac >~ jsonScientificKey) json
instance Json Int where
  json = jsonTyped jsonInt
  jsonKeyMap = jsonDict (jsonIntKey _BoundedInteger) json
instance Json Int8 where
  json = jsonTyped jsonInt8
  jsonKeyMap = jsonDict (jsonIntKey _BoundedInteger) json
instance Json Int16 where
  json = jsonTyped jsonInt16
  jsonKeyMap = jsonDict (jsonIntKey _BoundedInteger) json
instance Json Int32 where
  json = jsonTyped jsonInt32
  jsonKeyMap = jsonDict (jsonIntKey _BoundedInteger) json
instance Json Int64 where
  json = jsonTyped jsonInt64
  jsonKeyMap = jsonDict (jsonIntKey _BoundedInteger) json
instance Json Word where
  json = jsonTyped jsonWord
  jsonKeyMap = jsonDict (jsonIntKey _BoundedInteger) json
instance Json Word8 where
  json = jsonTyped jsonWord8
  jsonKeyMap = jsonDict (jsonIntKey _BoundedInteger) json
instance Json Word16 where
  json = jsonTyped jsonWord16
  jsonKeyMap = jsonDict (jsonIntKey _BoundedInteger) json
instance Json Word32 where
  json = jsonTyped jsonWord32
  jsonKeyMap = jsonDict (jsonIntKey _BoundedInteger) json
instance Json Word64 where
  json = jsonTyped jsonWord64
  jsonKeyMap = jsonDict (jsonIntKey _BoundedInteger) json
_Integer :: Prism' Scientific Integer
_Integer = prism' fromInteger $
  boundedScientific >=> either (const Nothing) Just . floatingOrInteger @Double
instance Json Integer where
  json = jsonTyped (_Integer ?< jsonNumber)
  jsonKeyMap = jsonDict (jsonIntKey _Integer) json
_Natural :: Prism' Scientific Natural
_Natural = prism' fromIntegral $ \s -> do
  i <- preview _Integer s
  fromInteger i <$ guard (i >= 0)
instance Json Natural where
  json = jsonTyped (_Natural ?< jsonNumber)
  jsonKeyMap = jsonDict (jsonIntKey _Natural) json
instance Json CTime where json = coerced >~ json @Int64
instance Json Version where
  json = jsonTyped jsonVersion
  jsonKeyMap = jsonDict jsonVersion json
instance Json a => Json (NonEmpty a) where
  json = prism' toList nonEmpty ?< jsonTuple (someP (jsonElem json))
instance Json a => Json (Solo a) where
  json = iso getSolo MkSolo >~ json @a
  jsonList = iso (map getSolo) (map MkSolo) >~ jsonList @a
  jsonKeyMap = iso (map (first' getSolo)) (map (first' MkSolo))
    >~ jsonKeyMap @a
  jsonKeyListMap = iso (map (first' (map getSolo))) (map (first' (map MkSolo)))
    >~ jsonKeyListMap @a
instance Json a => Json (Identity a) where
  json = coerced >~ json @a
  jsonList = coerced >~ jsonList @a
  jsonKeyMap = keysCoerced >~ jsonKeyMap @a
  jsonKeyListMap = keysCoerced >~ jsonKeyListMap @a
instance Json a => Json (Const a b) where
  json = coerced >~ json @a
  jsonKeyMap = keysCoerced >~ jsonKeyMap @a
instance Json (f (g a)) => Json (Compose f g a) where
  json = coerced >~ json @(f (g a))
instance (Json (f a), Json (g a)) => Json (Functor.Product f g a) where
  json = gtuple
instance (Json (f a), Json (g a)) => Json (Functor.Sum f g a) where
  json = iso
    (\case Functor.InL x -> Left x; Functor.InR y -> Right y)
    (either Functor.InL Functor.InR)
    >~ jsonTag "InL" json >+< jsonTag "InR" json
instance Json a => Json (Down a) where
  json = coerced >~ json @a
  jsonList = coerced >~ jsonList @a
instance Json a => Json (Monoid.Dual a) where
  json = coerced >~ json @a
  jsonList = coerced >~ jsonList @a
instance Json a => Json (Monoid.First a) where json = coerced >~ json @(Maybe a)
instance Json a => Json (Monoid.Last a) where json = coerced >~ json @(Maybe a)
instance Json a => Json (Semigroup.Min a) where
  json = coerced >~ json @a
  jsonList = coerced >~ jsonList @a
instance Json a => Json (Semigroup.Max a) where
  json = coerced >~ json @a
  jsonList = coerced >~ jsonList @a
instance Json a => Json (Semigroup.First a) where
  json = coerced >~ json @a
  jsonList = coerced >~ jsonList @a
instance Json a => Json (Semigroup.Last a) where
  json = coerced >~ json @a
  jsonList = coerced >~ jsonList @a
instance Json a => Json (Semigroup.WrappedMonoid a) where
  json = coerced >~ json @a
  jsonList = coerced >~ jsonList @a
instance Json a => Json (Semigroup.Sum a) where
  json = coerced >~ json @a
  jsonList = coerced >~ jsonList @a
instance Json a => Json (Semigroup.Product a) where
  json = coerced >~ json @a
  jsonList = coerced >~ jsonList @a
instance Json Semigroup.All where json = coerced >~ json @Bool
instance Json Semigroup.Any where json = coerced >~ json @Bool
instance Json (Proxy a) where json = dimap (const ()) (const Proxy) jsonNull
{- | The `GHC.Generic` `Json` grammar, defined as a `rule`
named by its `Typeable` type, so that each instantiation of
a parametric type is its own (possibly recursive) definition.
-}
instance (GHC.Generic a, GHC.Rep a ~ GHC.D1 d f, GSum f, Typeable a)
  => Json (GHC.Generically a) where
    json = dimap (\(GHC.Generically a) -> a) GHC.Generically $
      jsonTyped (dimap (GHC.unM1 . GHC.from) (GHC.to . GHC.M1) gsum)

-- tuples
instance (Json a, Json b) => Json (a, b) where
  json = jsonTuple (jsonElem json >*< jsonElem json)
instance (Json a, Json b, Json c) => Json (a, b, c) where json = gtuple
instance (Json a, Json b, Json c, Json d) => Json (a, b, c, d) where
  json = gtuple
instance (Json a, Json b, Json c, Json d, Json e) => Json (a, b, c, d, e) where
  json = gtuple
instance (Json a, Json b, Json c, Json d, Json e, Json f)
  => Json (a, b, c, d, e, f) where json = gtuple
instance (Json a, Json b, Json c, Json d, Json e, Json f, Json g)
  => Json (a, b, c, d, e, f, g) where json = gtuple
instance (Json a, Json b, Json c, Json d, Json e, Json f, Json g, Json h)
  => Json (a, b, c, d, e, f, g, h) where json = gtuple
instance
  ( Json a, Json b, Json c, Json d, Json e, Json f, Json g, Json h, Json i )
  => Json (a, b, c, d, e, f, g, h, i) where json = gtuple
instance
  ( Json a, Json b, Json c, Json d, Json e, Json f, Json g, Json h, Json i
  , Json j )
  => Json (a, b, c, d, e, f, g, h, i, j) where json = gtuple
instance
  ( Json a, Json b, Json c, Json d, Json e, Json f, Json g, Json h, Json i
  , Json j, Json k )
  => Json (a, b, c, d, e, f, g, h, i, j, k) where json = gtuple
instance
  ( Json a, Json b, Json c, Json d, Json e, Json f, Json g, Json h, Json i
  , Json j, Json k, Json l )
  => Json (a, b, c, d, e, f, g, h, i, j, k, l) where json = gtuple
instance
  ( Json a, Json b, Json c, Json d, Json e, Json f, Json g, Json h, Json i
  , Json j, Json k, Json l, Json m )
  => Json (a, b, c, d, e, f, g, h, i, j, k, l, m) where json = gtuple
instance
  ( Json a, Json b, Json c, Json d, Json e, Json f, Json g, Json h, Json i
  , Json j, Json k, Json l, Json m, Json n )
  => Json (a, b, c, d, e, f, g, h, i, j, k, l, m, n) where json = gtuple
instance
  ( Json a, Json b, Json c, Json d, Json e, Json f, Json g, Json h, Json i
  , Json j, Json k, Json l, Json m, Json n, Json o )
  => Json (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o) where json = gtuple

-- text
instance Json Text where
  json = jsonText
  jsonKeyMap = jsonDict jsonText json
instance Json LText.Text where
  json = iso LText.toStrict LText.fromStrict >~ jsonText
  jsonKeyMap =
    jsonDict (iso LText.toStrict LText.fromStrict >~ jsonText) json
instance Json ShortText where
  json = iso ShortText.toText ShortText.fromText >~ jsonText
  jsonKeyMap =
    jsonDict (iso ShortText.toText ShortText.fromText >~ jsonText) json

-- scientific
instance Json Scientific where
  json = jsonNumber
  jsonKeyMap = jsonDict jsonScientificKey json

-- containers
instance Json a => Json (Seq a) where
  json = iso toList Seq.fromList >~ jsonArray json
instance (Ord a, Json a) => Json (Set a) where
  json = iso Set.toList Set.fromList >~ jsonArray json
instance Json IntSet where
  json = iso IntSet.toList IntSet.fromList >~ json @[Int]
instance Json a => Json (IntMap a) where
  json = iso IntMap.toList IntMap.fromList >~ json @[(Int, a)]
instance (Ord k, Json k, Json v) => Json (Map k v) where
  json = iso Map.toList Map.fromList >~ jsonKeyMap @k
instance (Typeable a, Json a) => Json (Tree a) where
  json = jsonTyped gtuple

-- dlist
instance Json a => Json (DList a) where
  json = iso DList.toList DList.fromList >~ jsonArray json
instance Json a => Json (DNonEmpty a) where
  json = iso DNonEmpty.toNonEmpty DNonEmpty.fromNonEmpty >~ json @(NonEmpty a)

-- vector
instance Json a => Json (Vector a) where
  json = iso Vector.toList Vector.fromList >~ jsonArray json
instance (Storable a, Json a) => Json (VS.Vector a) where
  json = iso VG.toList VG.fromList >~ jsonArray json
instance (VP.Prim a, Json a) => Json (VP.Vector a) where
  json = iso VG.toList VG.fromList >~ jsonArray json
instance (VU.Unbox a, Json a) => Json (VU.Vector a) where
  json = iso VG.toList VG.fromList >~ jsonArray json

-- primitive
instance Json a => Json (Array a) where
  json = iso Exts.toList Exts.fromList >~ json @[a]
instance Json a => Json (SmallArray a) where
  json = iso Exts.toList Exts.fromList >~ json @[a]
instance (Prim a, Json a) => Json (PrimArray a) where
  json = iso Exts.toList Exts.fromList >~ json @[a]

-- unordered-containers
instance (Eq a, Hashable a, Json a) => Json (HashSet a) where
  json = iso HashSet.toList HashSet.fromList >~ jsonArray json
instance (Eq k, Hashable k, Json k, Json v) => Json (HashMap k v) where
  json = iso HashMap.toList HashMap.fromList >~ jsonKeyMap @k

-- aeson
instance Json Key where
  json = jsonKey
  jsonKeyMap = jsonDict jsonKey json
instance Json v => Json (KeyMap v) where
  json = iso KeyMap.toList KeyMap.fromList >~ jsonKeyMap @Key
instance Json Value where
  json = jsonValue
instance Json DotNetTime where
  json = jsonTyped (prism' render parse ?< jsonText)
    where
      render (DotNetTime t) = Text.pack
        ( formatTime defaultTimeLocale "/Date(%s" t
        <> take 3 (formatTime defaultTimeLocale "%q" t)
        <> ")/" )
      parse t =
        let (s, m) = Text.splitAt (Text.length t - 5) t
        in DotNetTime <$> parseTimeM True defaultTimeLocale
          "/Date(%s%Q)/" (Text.unpack (Text.concat [s, ".", m]))

-- time
instance Json Day where
  json = jsonTyped (jsonEncodedText _Day)
  jsonKeyMap = jsonDict (jsonEncodedText _Day) json
instance Json Month where
  json = jsonTyped (jsonEncodedText _Month)
  jsonKeyMap = jsonDict (jsonEncodedText _Month) json
instance Json Quarter where
  json = jsonTyped (jsonEncodedText _Quarter)
  jsonKeyMap = jsonDict (jsonEncodedText _Quarter) json
instance Json TimeOfDay where
  json = jsonTyped (jsonEncodedText _TimeOfDay)
  jsonKeyMap = jsonDict (jsonEncodedText _TimeOfDay) json
instance Json LocalTime where
  json = jsonTyped (jsonEncodedText _LocalTime)
  jsonKeyMap = jsonDict (jsonEncodedText _LocalTime) json
instance Json ZonedTime where
  json = jsonTyped (jsonEncodedText _ZonedTime)
  jsonKeyMap = jsonDict (jsonEncodedText _ZonedTime) json
instance Json UTCTime where
  json = jsonTyped (jsonEncodedText _UTCTime)
  jsonKeyMap = jsonDict (jsonEncodedText _UTCTime) json
instance Json NominalDiffTime where json = jsonTyped jsonRealFrac
instance Json DiffTime where json = jsonTyped jsonRealFrac
instance Json SystemTime where
  json = jsonTyped (prism' render parse ?< jsonNumber)
    where
      render (MkSystemTime s ns) =
        realToFrac (fromIntegral s + fromIntegral ns / 1000000000 :: Nano)
      parse sci = do
        n <- realToFrac <$> boundedScientific sci :: Maybe Nano
        let
          r = resolution n
          (s, ns) = floor (n * fromInteger r) `divMod` r
        Just (MkSystemTime (fromInteger s) (fromInteger ns))
instance Json CalendarDiffTime where
  json = dimap (\(CalendarDiffTime m t) -> (m, t)) (uncurry CalendarDiffTime)
    (jsonObject ("months" !: json >*< "time" !: json))
instance Json CalendarDiffDays where
  json = dimap (\(CalendarDiffDays m d) -> (m, d)) (uncurry CalendarDiffDays)
    (jsonObject ("months" !: json >*< "days" !: json))
instance Json DayOfWeek where
  json = jsonTyped (weekdays jsonEnum)
  jsonKeyMap = jsonDict (weekdays jsonEnumWith) json
instance Json QuarterOfYear where
  json = jsonTyped (quarters jsonEnum)
  jsonKeyMap = jsonDict (quarters jsonEnumWith) json

-- uuid-types
instance Json UUID where
  json = jsonTyped jsonUUID
  jsonKeyMap = jsonDict jsonUUID json

-- network-uri
instance Json URI where
  json = jsonTyped jsonURI
  jsonKeyMap = jsonDict jsonURI json

-- data-fix
instance (Typeable f, Json (f (Fix f))) => Json (Fix f) where
  json = jsonTyped (iso unFix Fix >~ json)
instance (Functor f, Typeable f, Json (f (Fix f))) => Json (Mu f) where
  json = iso (foldMu Fix) (unfoldMu unFix) >~ json @(Fix f)
instance (Functor f, Typeable f, Json (f (Fix f))) => Json (Nu f) where
  json = iso (foldNu Fix) (unfoldNu unFix) >~ json @(Fix f)

-- jsonTag
instance Json b => Json (Tagged a b) where
  json = coerced >~ json @b
  jsonKeyMap = keysCoerced >~ jsonKeyMap @b
  jsonKeyListMap = keysCoerced >~ jsonKeyListMap @b

-- these
instance (Json a, Json b) => Json (These a b) where
  json = orP
    [ _These >? jsonObject ("This" !: json >*< "That" !: json)
    , _This >? jsonTag "This" json
    , _That >? jsonTag "That" json
    ]
instance (Json (f a), Json (g a)) => Json (These1 f g a) where
  json = iso fromThese1 toThese1 >~ json @(These (f a) (g a))
    where
      fromThese1 = \case
        This1 a -> This a
        That1 b -> That b
        These1 a b -> These a b
      toThese1 = \case
        This a -> This1 a
        That b -> That1 b
        These a b -> These1 a b

-- strict
instance Json a => Json (Strict.Maybe a) where
  json = iso Strict.toLazy Strict.toStrict >~ json @(Maybe a)
instance (Json a, Json b) => Json (Strict.Either a b) where
  json = iso Strict.toLazy Strict.toStrict >~ json @(Either a b)
instance (Json a, Json b) => Json (Strict.These a b) where
  json = iso Strict.toLazy Strict.toStrict >~ json @(These a b)
instance (Json a, Json b) => Json (Strict.Pair a b) where
  json = iso Strict.toLazy Strict.toStrict >~ json @(a, b)

-- Generics

gsum :: forall f p x. (GSum f, JsonVal p) => p (f x) (f x)
gsum
  | gconCount @f == 1 = gsingle
  | Just names <- genum = names
  | otherwise = gjsonTag

class GSum f where
  gconCount :: Int
  gsingle :: JsonVal p => p (f x) (f x)
  -- | Constructor names, when all constructors are nullary.
  genum :: JsonVal p => Maybe (p (f x) (f x))
  gjsonTag :: JsonVal p => p (f x) (f x)

instance (GSum f, GSum g) => GSum (f GHC.:+: g) where
  gconCount = gconCount @f + gconCount @g
  gsingle = sumIso >~ gsingle >+< gsingle
  genum = liftA2 (\l r -> sumIso >~ l >+< r) genum genum
  gjsonTag = sumIso >~ gjsonTag >+< gjsonTag

sumIso :: Iso' ((f GHC.:+: g) x) (Either (f x) (g x))
sumIso = iso
  (\case GHC.L1 a -> Left a; GHC.R1 b -> Right b)
  (either GHC.L1 GHC.R1)

instance (GHC.Constructor c, GFields f, GContents f, GNullary f)
  => GSum (GHC.C1 c f) where
    gconCount = 1
    gsingle = GHC.M1 #. single .# GHC.unM1
      where
        single
          | GHC.conIsRecord (undefined :: GHC.C1 c f ()) = jsonObject gfields
          | otherwise = gcontents
    genum = gnullary @f <&> \v ->
      dimap (const ()) (const (GHC.M1 v)) (fromString (gconName @c))
    gjsonTag = GHC.M1 #. jsonObject (tag >* contents) .# GHC.unM1
      where
        tag :: JsonObj p q => q () ()
        tag = "tag" !: fromString (gconName @c)
        contents :: JsonObj p q => q (f x) (f x)
        contents
          | GHC.conIsRecord (undefined :: GHC.C1 c f ()) = gfields
          | Just v <- gnullary @f = dimap (const ()) (const v) oneP
          | otherwise = "contents" !: gcontents

gconName :: forall (c :: GHC.Meta). GHC.Constructor c => String
gconName = GHC.conName (undefined :: GHC.C1 c GHC.U1 ())

gselName :: forall (s :: GHC.Meta). GHC.Selector s => String
gselName = GHC.selName (undefined :: GHC.S1 s GHC.U1 ())

class GFields f where
  gfields :: JsonObj p q => q (f x) (f x)
instance (GHC.Selector s, Json a) => GFields (GHC.S1 s (GHC.K1 i a)) where
  gfields = (GHC.M1 . GHC.K1) #. (Text.pack (gselName @s) !: json)
    .# GHC.unK1 . GHC.unM1
instance (GFields f, GFields g) => GFields (f GHC.:*: g) where
  gfields = dimap2
    (\(a GHC.:*: _) -> a) (\(_ GHC.:*: b) -> b) (GHC.:*:) gfields gfields
instance GFields GHC.U1 where
  gfields = dimap (const ()) (const GHC.U1) oneP

class GElements f where
  gelements :: JsonTup p q => q (f x) (f x)
instance Json a => GElements (GHC.S1 s (GHC.K1 i a)) where
  gelements = (GHC.M1 . GHC.K1) #. jsonElem json .# GHC.unK1 . GHC.unM1
instance (GElements f, GElements g) => GElements (f GHC.:*: g) where
  gelements = dimap2
    (\(a GHC.:*: _) -> a) (\(_ GHC.:*: b) -> b) (GHC.:*:) gelements gelements
instance GElements GHC.U1 where
  gelements = dimap (const ()) (const GHC.U1) oneP

-- | The `GHC.Generic` tuple of a single constructor's positional fields.
gtuple
  :: (GHC.Generic a, GHC.Rep a ~ GHC.D1 d (GHC.C1 c f), GElements f, JsonVal p)
  => p a a
gtuple = dimap (GHC.unM1 . GHC.unM1 . GHC.from) (GHC.to . GHC.M1 . GHC.M1)
  (jsonTuple gelements)

class GContents f where
  gcontents :: JsonVal p => p (f x) (f x)
instance Json a => GContents (GHC.S1 s (GHC.K1 i a)) where
  gcontents = (GHC.M1 . GHC.K1) #. json .# GHC.unK1 . GHC.unM1
instance (GElements f, GElements g) => GContents (f GHC.:*: g) where
  gcontents = jsonTuple gelements
instance GContents GHC.U1 where
  gcontents = jsonTuple gelements

class GNullary f where
  gnullary :: Maybe (f x)
instance GNullary GHC.U1 where
  gnullary = Just GHC.U1
instance GNullary (GHC.S1 s f) where
  gnullary = Nothing
instance GNullary (f GHC.:*: g) where
  gnullary = Nothing
