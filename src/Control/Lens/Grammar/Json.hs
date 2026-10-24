{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RequiredTypeArguments #-}

module Control.Lens.Grammar.Json
  ( -- * Json
    Json (..)
  , JsonVal (..)
  , JsonString (..)
  , JsonTup (..)
  , JsonObj (..)
  , jsonRule
    -- * Aeson
  , jsonParse
  , jsonPrint
  , jsonEncode
  , JsonError (..)
  , JsonErrorKind (..)
  , jsonErrorMessage
    -- * TypeScript
  , jsonType
  , jsonTypeScript
  , TsDeclarations (..)
  , TsType (..)
  , TsElement (..)
  , TsProperty (..)
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.Grammar
import Control.Monad
import Control.Monad.Trans.Except (ExceptT (..))
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State.Strict
import Data.Aeson.Encoding (Encoding)
import Data.Aeson.Encoding qualified as Encoding
import Data.Aeson.Key (Key)
import Data.Aeson.Key qualified as Key
import Data.Aeson.KeyMap (KeyMap)
import Data.Aeson.KeyMap qualified as KeyMap
import Data.Aeson.Text (encodeToLazyText)
import Data.Aeson.Types
  (DotNetTime (..), JSONPathElement (..), Object, Value (..))
import Data.Bifunctor.Joker
import Data.ByteString.Lazy qualified as LByteString
import Data.Char (isAlpha, isAlphaNum, isDigit)
import Data.Coerce
import Data.DList (DList)
import Data.DList qualified as DList
import Data.DList.DNonEmpty (DNonEmpty)
import Data.DList.DNonEmpty qualified as DNonEmpty
import Data.Fix (Fix (..), Mu, Nu, foldMu, foldNu, unfoldMu, unfoldNu)
import Data.Fixed (Fixed, HasResolution (..), Nano)
import Data.Foldable (toList)
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
import Data.List (find, findIndices, intercalate, nub)
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
import Data.Proxy (Proxy (..))
import Data.Ratio (Ratio, denominator, numerator, (%))
import Data.Scientific
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
import Data.Tree (Tree (..))
import Data.Tuple (Solo (MkSolo), getSolo)
import Data.Typeable
  ( TypeRep, Typeable, tyConModule, tyConName, typeRep, typeRepArgs
  , typeRepTyCon
  )
import Data.UUID.Types (UUID)
import Data.UUID.Types qualified as UUID
import Data.Vector (Vector)
import Data.Vector qualified as Vector
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

-- Json grammars --

{- | `Json` grammars, compatible with @aeson@'s
@ToJSON@ & @FromJSON@ instances.
`jsonList` mirrors @aeson@'s @toJSONList@,
so that `String`s are JSON strings rather than arrays.
`jsonKeyMap` & `jsonKeyListMap` mirror @aeson@'s
@toJSONKey@ & @toJSONKeyList@, so that maps with textual keys
are JSON objects rather than arrays of key-value pairs.
-}
class Json a where
  json :: JsonVal p => p a a
  default json :: (Json (GHC.Generically a), JsonVal p) => p a a
  json = iso GHC.Generically (\(GHC.Generically a) -> a) >~ json
  jsonList :: JsonVal p => p [a] [a]
  jsonList = jsonArray json
  jsonKeyMap :: (Json v, JsonVal p) => p [(a, v)] [(a, v)]
  jsonKeyMap = jsonKeyValues json
  jsonKeyListMap :: (Json v, JsonVal p) => p [([a], v)] [([a], v)]
  jsonKeyListMap = jsonKeyValues jsonList

{- | `JsonVal` grammars describe JSON values.
A `jsonTypeRule` is a `rule` for a Haskell type,
named by its `TypeRep`, like a type definition.
-}
class
  ( CocartesianChoice p
  , JsonString p
  , forall x y. BackusNaurForm (p x y)
  ) => JsonVal p where
  jsonNull :: p () ()
  jsonBool :: p Bool Bool
  jsonNumber :: p Scientific Scientific
  jsonInt :: p Int Int
  jsonInt = numeric fromIntegral toBoundedInteger
  jsonDouble :: p Double Double
  jsonDouble = numeric fromFloatDigits (Just . toRealFloat)
  jsonArray :: p a b -> p [a] [b]
  jsonDict
    :: (forall q. JsonString q => q a b)
    -> p c d -> p [(a, c)] [(b, d)]
  jsonTuple :: (forall q. JsonTup q => q a b) -> p a b
  jsonObject :: (forall q. JsonObj q => q a b) -> p a b
  jsonTypeRule :: TypeRep -> p a b -> p a b
  jsonTypeRule = rule . show

{- | `JsonString`s have string literals, exactly matching some text.
They're determined by `Cochoice` partiality.

prop> fromString s = only (Text.pack s) ?< jsonString
-}
class
  ( Choice p, Cochoice p
  , forall x y. (x ~ (), y ~ ()) => IsString (p x y)
  ) => JsonString p where
  jsonString :: p Text Text

{- | `JsonTup` grammars describe the elements of a JSON array.
As `Distributor`s they have optional elements (`optionalP`),
rest elements (`manyP`) and alternative elements (`>+<`),
like TypeScript's variadic tuple types, @[A, B?, ...C[]]@.
-}
class Distributor p => JsonTup p where
  jsonVal :: (forall q. JsonVal q => q a b) -> p a b

{- | `JsonObj` grammars describe the properties of a JSON object.
Each key may be read or written at most once.
An optional property may be missing, like TypeScript's @{k?: T}@.
-}
class Monoidal p => JsonObj p where
  jsonKeyVal :: Text -> (forall q. JsonVal q => q a b) -> p a b
  jsonOptionalKeyVal
    :: Text -> (forall q. JsonVal q => q a b) -> p (Maybe a) (Maybe b)

-- | A `jsonTypeRule` for a `Typeable` type.
jsonRule :: forall a p. (Typeable a, JsonVal p) => p a a -> p a a
jsonRule = jsonTypeRule (typeRep (Proxy @a))

jsonKeyValues
  :: (Json v, JsonVal p)
  => (forall q. JsonVal q => q a a) -> p [(a, v)] [(a, v)]
jsonKeyValues key = jsonArray $ jsonTuple $
  (,) <$> lmap fst (jsonVal key) <*> lmap snd (jsonVal json)

jsonKeyText
  :: (Json v, JsonVal p)
  => (forall q. JsonString q => q a a) -> p [(a, v)] [(a, v)]
jsonKeyText key = jsonDict key json

keysCoerced :: Coercible k a => Iso' [(k, v)] [(a, v)]
keysCoerced = iso (map (first' coerce)) (map (first' coerce))

-- Running Json grammars --

jsonParse :: Json a => Value -> Either JsonError a
jsonParse = runJsonParsor json

jsonPrint :: Json a => a -> Either JsonError Value
jsonPrint = runJsonPrintor json

-- | Print directly to an @aeson@ `Encoding`, like @toEncoding@.
jsonEncode :: Json a => a -> Either JsonError Encoding
jsonEncode = runJsonPrintor json


{- | The TypeScript type of a `Json` grammar, with type aliases for
its `jsonTypeRule`s, each of which is named uniquely and declared once.
-}
jsonType :: forall a -> Json a => TsDeclarations
jsonType a = tsDeclarations (json @a)

-- | TypeScript type declarations of a `Json` grammar.
jsonTypeScript :: forall a -> (Json a, Typeable a) => Text
jsonTypeScript a = renderTypeScript (show (typeRep (Proxy @a))) (jsonType a)

-- Errors --

{- | A located failure to parse or print a `Value`.
Its path is relative to that `Value`, root first.
It expected one of the alternatives, none meaning just "unexpected".
Parsing found a `Value`; printing doesn't show the Haskell value it found.
-}
data JsonError = JsonError
  { jsonErrorPath :: [JSONPathElement]
  , jsonErrorExpected :: [String]
  , jsonErrorFound :: Maybe Value
  , jsonErrorKind :: JsonErrorKind
  } deriving stock (Eq, Show)

data JsonErrorKind
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
    | jsonErrorKind err == JsonMissing ->
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
jsonUnexpected found = Left (JsonError [] [] found JsonMismatch)

jsonMismatch :: String -> Value -> Either JsonError a
jsonMismatch expected found =
  Left (JsonError [] [expected] (Just found) JsonMismatch)

jsonMissing :: String -> Maybe Value -> Either JsonError a
jsonMissing expected found = Left (JsonError [] [expected] found JsonMissing)

countElements :: Int -> String
countElements n = show n <> if n == 1 then " element" else " elements"

jsonAt :: JSONPathElement -> Either JsonError a -> Either JsonError a
jsonAt el = left' (\err -> err {jsonErrorPath = el : jsonErrorPath err})

-- | A `rule` labels its failures, like @(\<?\>)@ for parser combinators.
jsonRelabel :: String -> JsonError -> JsonError
jsonRelabel name err
  | null (jsonErrorPath err)
  , jsonErrorKind err /= JsonMissing = err {jsonErrorExpected = [name]}
  | otherwise = err

{- | Combine the failures of alternatives: the deepest failure wins,
failures on the same value merge their expectations,
and a string literal mismatch loses to any other failure.
-}
jsonOrElse :: JsonError -> JsonError -> JsonError
jsonOrElse err1 err2
  | depth1 /= depth2 = if depth1 > depth2 then err1 else err2
  | jsonErrorPath err1 == jsonErrorPath err2
  , jsonErrorFound err1 == jsonErrorFound err2 = err2
    { jsonErrorExpected =
        nub (jsonErrorExpected err1 <> jsonErrorExpected err2)
    , jsonErrorKind = max (jsonErrorKind err1) (jsonErrorKind err2)
    }
  | jsonErrorKind err2 == JsonLiteral
  , jsonErrorKind err1 /= JsonLiteral = err1
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
  v -> Left (JsonError [] (literals table) (Just v) JsonLiteral)
dispatching (Dispatch (Just key) table) = \case
  v@(Object o) -> case KeyMap.lookup key o of
    Nothing -> jsonMissing ("key " <> showKey key) (Just v)
    Just (String t) | Just p <- Map.lookup t table -> p v
    Just tag ->
      Left (JsonError [Key key] (literals table) (Just tag) JsonLiteral)
  v -> jsonMismatch "object" v

literals :: Map Text a -> [String]
literals = map show . Map.keys

orElse
  :: (Value -> Either JsonError b) -> (Value -> Either JsonError b)
  -> Value -> Either JsonError b
orElse p q v = case p v of
  Left err1 -> left' (jsonOrElse err1) (q v)
  success -> success

{- | `TupParsor` parses the elements of a JSON array from a position,
in every way it can, so that optional and rest elements backtrack.
-}
newtype TupParsor a b = TupParsor
  {runTupParsor :: Vector Value -> Int -> [Either JsonError (b, Int)]}

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
  fmap f = mapParsing (fmap (fmap f))
instance Profunctor JsonParsor where
  dimap _ g = mapParsing (fmap (fmap g))
instance Choice JsonParsor where
  left' = mapParsing (fmap (fmap Left))
  right' = mapParsing (fmap (fmap Right))
instance Cochoice JsonParsor where
  unleft = mapParsing $ \p v ->
    p v >>= either pure (\_ -> jsonUnexpected (Just v))
  unright = mapParsing $ \p v ->
    p v >>= either (\_ -> jsonUnexpected (Just v)) pure
instance CocartesianMonoidal JsonParsor where
  zeroP = emptyP
  p >+< q = altP (Left <$> coerce p) (Right <$> coerce q)
instance CocartesianChoice JsonParsor where
  emptyP = jsonParsor (jsonUnexpected . Just)
  altP p q = case (jsonParsorDispatch p, jsonParsorDispatch q) of
    (Just dispatch0, Just dispatch1)
      | dispatchKey dispatch0 == dispatchKey dispatch1 ->
          let
            dispatch = Dispatch (dispatchKey dispatch0) $ Map.unionWith orElse
              (dispatchTable dispatch0) (dispatchTable dispatch1)
          in
            JsonParsor (Just dispatch) (dispatching dispatch)
    _ -> jsonParsor (orElse (runJsonParsor p) (runJsonParsor q))
instance BackusNaurForm (JsonParsor a b) where
  rule name = mapParsing (left' (jsonRelabel name) .)
  ruleRec name f = fix (rule name . f)
instance (x ~ (), y ~ ()) => IsString (JsonParsor x y) where
  fromString s = JsonParsor
    (Just (Dispatch Nothing (Map.singleton literal parse))) parse
    where
      literal = Text.pack s
      parse = \case
        String t | t == literal -> Right ()
        v -> Left (JsonError [] [show s] (Just v) JsonLiteral)
instance JsonString JsonParsor where
  jsonString = jsonParsor $ \case
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
  jsonArray p = jsonParsor $ \case
    Array arr -> zipWithM
      (\i v -> jsonAt (Index i) (runJsonParsor p v)) [0 ..] (Vector.toList arr)
    v -> jsonMismatch "array" v
  jsonDict key p = jsonParsor $ \case
    Object o -> for (KeyMap.toList o) $ \(k, v) -> jsonAt (Key k) $
      (,) <$> runJsonParsor key (String (Key.toText k)) <*> runJsonParsor p v
    v -> jsonMismatch "object" v
  jsonTuple tup = jsonParsor $ \case
    Array arr ->
      let
        outcomes = runTupParsor tup arr 0
        incomplete = \case
          Left err -> err
          Right (_, n) ->
            JsonError [] [countElements n] (Just (Array arr)) JsonMissing
      in
        case [b | Right (b, n) <- outcomes, n == Vector.length arr] of
          b : _ -> Right b
          [] -> Left (foldl jsonOrElse unexpected (map incomplete outcomes))
            where
              unexpected = JsonError [] [] (Just (Array arr)) JsonMismatch
    v -> jsonMismatch "array" v
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

deriving via ReaderT (Vector Value) (StateT Int (ExceptT JsonError []))
  instance Functor (TupParsor a)
deriving via ReaderT (Vector Value) (StateT Int (ExceptT JsonError []))
  instance Applicative (TupParsor a)
deriving via Joker (ReaderT (Vector Value) (StateT Int (ExceptT JsonError [])))
  instance Profunctor TupParsor
instance CocartesianMonoidal TupParsor where
  zeroP = TupParsor (\_ _ -> [])
  TupParsor p >+< TupParsor q = TupParsor $ \arr i ->
    map (fmap (first' Left)) (p arr i) <> map (fmap (first' Right)) (q arr i)
-- | `manyP` tries longer repetitions first, never repeating an empty match.
instance Distributor TupParsor where
  manyP (TupParsor p) = TupParsor go
    where
      go arr i = concatMap step (p arr i) <> [Right ([], i)]
        where
          step = \case
            Left err -> [Left err]
            Right (b, j) | j > i -> map (fmap (first' (b :))) (go arr j)
            Right _ -> []
instance JsonTup TupParsor where
  jsonVal p = TupParsor $ \arr i -> pure $ case arr Vector.!? i of
    Nothing ->
      jsonMissing ("at least " <> countElements (i + 1)) (Just (Array arr))
    Just v -> (, i + 1) <$> jsonAt (Index i) (runJsonParsor p v)

instance Functor (ObjParsor a) where
  fmap f (ObjParsor keys tags p) = ObjParsor keys tags (fmap f . p)
instance Applicative (ObjParsor a) where
  pure b = ObjParsor [] [] (\_ -> Right b)
  ObjParsor keys0 tags0 p0 <*> ObjParsor keys1 tags1 p1 =
    ObjParsor (keys0 <> keys1) (tags0 <> tags1) (\o -> p0 o <*> p1 o)
instance Profunctor ObjParsor where
  dimap _ g (ObjParsor keys tags p) = ObjParsor keys tags (fmap g . p)
instance JsonObj ObjParsor where
  jsonKeyVal k p = ObjParsor [key] tags $ \o -> case KeyMap.lookup key o of
    Nothing -> jsonMissing ("key " <> show k) (Just (Object o))
    Just v -> jsonAt (Key key) (runJsonParsor p v)
    where
      key = Key.fromText k
      tags = case jsonParsorDispatch p of
        Just (Dispatch Nothing table) -> [(key, Map.keysSet table)]
        _ -> []
  jsonOptionalKeyVal k p = ObjParsor [key] [] $ \o ->
    traverse (jsonAt (Key key) . runJsonParsor p) (KeyMap.lookup key o)
    where
      key = Key.fromText k

duplicateKey :: [Key] -> Maybe Key
duplicateKey = go Set.empty
  where
    go _ [] = Nothing
    go seen (key : keys)
      | Set.member key seen = Just key
      | otherwise = go (Set.insert key seen) keys

showKey :: Key -> String
showKey = show . Key.toText

-- Printing interpreters --

-- | @aeson@'s representations of JSON values, `Value` & `Encoding`.
class AesonVal val where
  aesonNull :: val
  aesonBool :: Bool -> val
  aesonNumber :: Scientific -> val
  aesonInt :: Int -> val
  aesonDouble :: Double -> val
  aesonString :: Text -> val
  aesonArray :: [val] -> val
  aesonObject :: [(Key, val)] -> val

instance AesonVal Value where
  aesonNull = Null
  aesonBool = Bool
  aesonNumber = Number
  aesonInt = Number . fromIntegral
  aesonDouble = Number . fromFloatDigits
  aesonString = String
  aesonArray = Array . Vector.fromList
  aesonObject = Object . KeyMap.fromList

instance AesonVal Encoding where
  aesonNull = Encoding.null_
  aesonBool = Encoding.bool
  aesonNumber = Encoding.scientific
  aesonInt = Encoding.int
  aesonDouble = Encoding.double
  aesonString = Encoding.text
  aesonArray = Encoding.list id
  aesonObject = Encoding.pairs . foldMap (uncurry Encoding.pair)

newtype JsonPrintor val a b = JsonPrintor
  {runJsonPrintor :: a -> Either JsonError val}

newtype TupPrintor val a b = TupPrintor
  {runTupPrintor :: a -> Int -> Either JsonError ([val], Int)}

{- | `ObjPrintor` writes keys of an `Object`.
Its keys are known before printing, so overlapping keys are found once.
-}
data ObjPrintor val a b = ObjPrintor
  { objPrintorKeys :: [Key]
  , runObjPrintor :: a -> Either JsonError [(Key, val)]
  }

printObject :: AesonVal val => [(Key, val)] -> Either JsonError val
printObject props = case duplicateKey (map fst props) of
  Just key -> printDuplicate key
  Nothing -> Right (aesonObject props)

printDuplicate :: Key -> Either JsonError a
printDuplicate key = jsonMissing ("key " <> showKey key <> " twice") Nothing

deriving via Forget (Either JsonError val) a
  instance Functor (JsonPrintor val a)
deriving via Forget (Either JsonError val)
  instance Profunctor (JsonPrintor val)
deriving via Forget (Either JsonError val)
  instance Cochoice (JsonPrintor val)
deriving via Forget (Either JsonError val)
  instance CocartesianMonoidal (JsonPrintor val)
instance Choice (JsonPrintor val) where
  left' (JsonPrintor p) =
    JsonPrintor (either p (\_ -> jsonUnexpected Nothing))
  right' (JsonPrintor p) =
    JsonPrintor (either (\_ -> jsonUnexpected Nothing) p)
instance CocartesianChoice (JsonPrintor val) where
  emptyP = JsonPrintor (\_ -> jsonUnexpected Nothing)
  altP (JsonPrintor p) (JsonPrintor q) = JsonPrintor $ \a -> case p a of
    Left err1 -> left' (jsonOrElse err1) (q a)
    success -> success
instance BackusNaurForm (JsonPrintor val a b) where
  rule name (JsonPrintor p) = JsonPrintor (left' (jsonRelabel name) . p)
  ruleRec name f = fix (rule name . f)
instance (AesonVal val, x ~ (), y ~ ()) => IsString (JsonPrintor val x y) where
  fromString s = JsonPrintor (const (Right (aesonString (Text.pack s))))
instance AesonVal val => JsonString (JsonPrintor val) where
  jsonString = JsonPrintor (Right . aesonString)
instance AesonVal val => JsonVal (JsonPrintor val) where
  jsonNull = JsonPrintor (const (Right aesonNull))
  jsonBool = JsonPrintor (Right . aesonBool)
  jsonNumber = JsonPrintor (Right . aesonNumber)
  jsonInt = JsonPrintor (Right . aesonInt)
  jsonDouble = JsonPrintor (Right . aesonDouble)
  jsonArray (JsonPrintor p) = JsonPrintor $ \as ->
    aesonArray <$> zipWithM (\i a -> jsonAt (Index i) (p a)) [0 ..] as
  jsonDict key (JsonPrintor p) = JsonPrintor (traverse entry >=> printObject)
    where
      entry (a, c) = do
        k <- printKey a
        (k,) <$> jsonAt (Key k) (p c)
      printKey a = runJsonPrintor (key @(JsonPrintor Value)) a >>= \case
        String t -> Right (Key.fromText t)
        _ -> jsonMissing "key as a string" Nothing
  jsonTuple tup = JsonPrintor $ \a ->
    aesonArray . fst <$> runTupPrintor tup a 0
  jsonObject obj = JsonPrintor $ case duplicateKey (objPrintorKeys printor) of
    Just key -> \_ -> printDuplicate key
    Nothing -> fmap aesonObject . runObjPrintor printor
    where
      printor = obj @(ObjPrintor val)

deriving via Forget (Ap (StateT Int (Either JsonError)) [val]) a
  instance Functor (TupPrintor val a)
deriving via Forget (Ap (StateT Int (Either JsonError)) [val]) a
  instance Applicative (TupPrintor val a)
deriving via Forget (Ap (StateT Int (Either JsonError)) [val])
  instance Profunctor (TupPrintor val)
deriving via Forget (Ap (StateT Int (Either JsonError)) [val])
  instance CocartesianMonoidal (TupPrintor val)
deriving via Forget (Ap (StateT Int (Either JsonError)) [val])
  instance Distributor (TupPrintor val)
instance AesonVal val => JsonTup (TupPrintor val) where
  jsonVal p = TupPrintor $ \a i ->
    (\printed -> ([printed], i + 1)) <$> jsonAt (Index i) (runJsonPrintor p a)

instance Functor (ObjPrintor val a) where
  fmap _ (ObjPrintor keys p) = ObjPrintor keys p
instance Applicative (ObjPrintor val a) where
  pure _ = ObjPrintor [] (\_ -> Right [])
  ObjPrintor keys0 p0 <*> ObjPrintor keys1 p1 =
    ObjPrintor (keys0 <> keys1) (\a -> (<>) <$> p0 a <*> p1 a)
instance Profunctor (ObjPrintor val) where
  dimap f _ (ObjPrintor keys p) = ObjPrintor keys (p . f)
instance AesonVal val => JsonObj (ObjPrintor val) where
  jsonKeyVal k p = ObjPrintor [key] (printProperty key p)
    where
      key = Key.fromText k
  jsonOptionalKeyVal k p =
    ObjPrintor [key] (maybe (Right []) (printProperty key p))
    where
      key = Key.fromText k

printProperty
  :: Key -> JsonPrintor val a b -> a -> Either JsonError [(Key, val)]
printProperty key p a =
  (\printed -> [(key, printed)]) <$> jsonAt (Key key) (runJsonPrintor p a)

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
  deriving stock (Eq, Ord, Show, Read)

data TsElement
  = TsRequired TsType -- ^ @T@
  | TsOptional TsType -- ^ @T?@
  | TsRest TsType -- ^ @...T[]@
  deriving stock (Eq, Ord, Show, Read)

-- | A TypeScript type, with the type aliases it refers to.
data TsDeclarations = TsDeclarations
  { tsRootType :: TsType
  , tsTypeAliases :: Map String TsType
  } deriving stock (Eq, Show, Read)

-- | A property of a TypeScript object type, @abc: T@ or @abc?: T@.
data TsProperty = TsProperty
  { tsPropertyName :: Text
  , tsPropertyIsOptional :: Bool
  , tsPropertyType :: TsType
  } deriving stock (Eq, Ord, Show, Read)

newtype TsGrammor a b = TsGrammor (State TsDefinitions TsType)

newtype TsTupGrammor a b = TsTupGrammor
  {runTsTupGrammor :: Ap (State TsDefinitions) TsShapes}

newtype TsObjGrammor a b = TsObjGrammor
  {runTsObjGrammor :: Ap (State TsDefinitions) [TsProperty]}

data TsDefinitions = TsDefinitions
  { tsRuleNames :: Map TsRuleKey String
  , tsRules :: Map String TsType
  }

data TsRuleKey = TsNamedRule String | TsTypedRule TypeRep
  deriving stock (Eq, Ord)

tsDeclarations :: TsGrammor a b -> TsDeclarations
tsDeclarations (TsGrammor ts) = TsDeclarations root (tsRules definitions)
  where
    (root, definitions) = runState ts (TsDefinitions Map.empty Map.empty)

{- | Define a rule once, under the first of its names which isn't taken,
so that every other occurrence of it, recursive or not, is its name.
-}
tsDefine :: TsRuleKey -> [String] -> TsGrammor a b -> TsGrammor c d
tsDefine key names (TsGrammor body) = TsGrammor $ do
  known <- gets (Map.lookup key . tsRuleNames)
  case known of
    Just name -> pure (TsAlias name)
    Nothing -> do
      taken <- gets (Set.fromList . Map.elems . tsRuleNames)
      let name = freshName taken names
      modify (nameRule key name)
      definition <- body
      modify (defineRule name definition)
      pure (TsAlias name)

nameRule :: TsRuleKey -> String -> TsDefinitions -> TsDefinitions
nameRule key name defs =
  defs {tsRuleNames = Map.insert key name (tsRuleNames defs)}

defineRule :: String -> TsType -> TsDefinitions -> TsDefinitions
defineRule name definition defs =
  defs {tsRules = Map.insert name definition (tsRules defs)}

freshName :: Set String -> [String] -> String
freshName taken names = fromMaybe primed (find (`Set.notMember` taken) names)
  where
    primed = until (`Set.notMember` taken) (<> "'") (last names)

qualifiedTypeName :: TypeRep -> String
qualifiedTypeName rep = case typeRepArgs rep of
  [] -> constructor
  args -> unwords (constructor : map typeArgument args)
  where
    tyCon = typeRepTyCon rep
    constructor = tyConModule tyCon <> "." <> tyConName tyCon
    typeArgument arg = case typeRepArgs arg of
      [] -> qualifiedTypeName arg
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

tsAlternatives :: TsGrammor a b -> TsGrammor c d -> TsGrammor s t
tsAlternatives (TsGrammor t0) (TsGrammor t1) =
  TsGrammor (liftA2 (\a b -> tsUnion [a, b]) t0 t1)

tsObject :: [TsProperty] -> TsType
tsObject props
  | length (nub names) == length names = TsObject props
  | otherwise = tsUnion []
  where
    names = map tsPropertyName props

{- | Alternative shapes of a TypeScript tuple type,
so that `>*<` concatenates each pair of shapes and `>+<` unites them.
-}
newtype TsShapes = TsShapes [[TsElement]]
instance Semigroup TsShapes where
  TsShapes s0 <> TsShapes s1 = TsShapes (liftA2 (<>) s0 s1)
instance Monoid TsShapes where
  mempty = TsShapes [[]]

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
-}
tsTuple :: TsShapes -> TsType
tsTuple (TsShapes shapes) =
  tsUnion (TsTuple <$> nub (concatMap (expand False . mergeRests) shapes))
  where
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

deriving via Grammor (State TsDefinitions TsType) a
  instance Functor (TsGrammor a)
deriving via Grammor (State TsDefinitions TsType)
  instance Profunctor TsGrammor
deriving via Grammor (State TsDefinitions TsType)
  instance Choice TsGrammor
instance Cochoice TsGrammor where
  unleft = coerce
  unright = coerce
instance CocartesianMonoidal TsGrammor where
  zeroP = emptyP
  (>+<) = tsAlternatives
instance CocartesianChoice TsGrammor where
  emptyP = tsType (tsUnion [])
  altP = tsAlternatives
instance BackusNaurForm (TsGrammor a b) where
  rule name = tsDefine (TsNamedRule name) [name]
  ruleRec name f = rule name (f self)
    where
      self = TsGrammor (gets (TsAlias . ruleName))
      ruleName = Map.findWithDefault name (TsNamedRule name) . tsRuleNames
instance (x ~ (), y ~ ()) => IsString (TsGrammor x y) where
  fromString = tsType . TsLiteral . Text.pack
instance JsonString TsGrammor where
  jsonString = tsType TsString
instance JsonVal TsGrammor where
  jsonNull = tsType TsNull
  jsonBool = tsType TsBoolean
  jsonNumber = tsType TsNumber
  jsonArray (TsGrammor t) = TsGrammor (TsArray <$> t)
  jsonDict _ (TsGrammor t) = TsGrammor (TsDict <$> t)
  jsonTuple tup = TsGrammor (tsTuple <$> getAp (runTsTupGrammor tup))
  jsonObject obj = TsGrammor (tsObject <$> getAp (runTsObjGrammor obj))
  jsonTypeRule rep =
    tsDefine (TsTypedRule rep) [show rep, qualifiedTypeName rep]

deriving via Grammor (Ap (State TsDefinitions) TsShapes) a
  instance Functor (TsTupGrammor a)
deriving via Grammor (Ap (State TsDefinitions) TsShapes) a
  instance Applicative (TsTupGrammor a)
deriving via Grammor (Ap (State TsDefinitions) TsShapes)
  instance Profunctor TsTupGrammor
instance CocartesianMonoidal TsTupGrammor where
  zeroP = TsTupGrammor (pure (TsShapes []))
  TsTupGrammor s0 >+< TsTupGrammor s1 = TsTupGrammor (liftA2 unite s0 s1)
    where
      unite (TsShapes shapes0) (TsShapes shapes1) =
        TsShapes (shapes0 <> shapes1)
{- | `optionalP` is an optional element, of a single required element,
or else an alternative empty shape. `manyP` is a rest element,
of the union of the elements of its shapes.
-}
instance Distributor TsTupGrammor where
  optionalP (TsTupGrammor s) = TsTupGrammor (optionalShape <$> s)
    where
      optionalShape (TsShapes shapes) =
        TsShapes $ case traverse single shapes of
          Just ts@(_ : _) -> [[TsOptional (tsUnion ts)]]
          _ -> [] : shapes
      single = \case
        [TsRequired t] -> Just t
        _ -> Nothing
  manyP (TsTupGrammor s) = TsTupGrammor (rest <$> s)
    where
      rest (TsShapes shapes) = TsShapes $
        case concatMap (map tsElementType) shapes of
          [] -> [[]]
          ts -> [[TsRest (tsUnion ts)]]
instance JsonTup TsTupGrammor where
  jsonVal (TsGrammor t) =
    TsTupGrammor (Ap ((\ty -> TsShapes [[TsRequired ty]]) <$> t))

deriving via Grammor (Ap (State TsDefinitions) [TsProperty]) a
  instance Functor (TsObjGrammor a)
deriving via Grammor (Ap (State TsDefinitions) [TsProperty]) a
  instance Applicative (TsObjGrammor a)
deriving via Grammor (Ap (State TsDefinitions) [TsProperty])
  instance Profunctor TsObjGrammor
instance JsonObj TsObjGrammor where
  jsonKeyVal k (TsGrammor t) =
    TsObjGrammor (Ap (pure . TsProperty k False <$> t))
  jsonOptionalKeyVal k (TsGrammor t) =
    TsObjGrammor (Ap (pure . TsProperty k True <$> t))

-- Rendering TypeScript --

{- | Render TypeScript type alias declarations, including one named
@rootName@ for the root type, unless it's already a type alias.
-}
renderTypeScript :: String -> TsDeclarations -> Text
renderTypeScript rootName (TsDeclarations root aliases) =
  Text.unlines (map declaration (Map.toList declarations))
  where
    declarations = case root of
      TsAlias _ -> aliases
      _ -> Map.insert rootName root aliases
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

textual :: JsonString p => (a -> Text) -> (Text -> Maybe a) -> p a a
textual f g = prism' f g ?< jsonString

textEnum :: JsonString p => (a -> Text) -> [a] -> p a a
textEnum f as = textual f (\t -> lookup t [(f a, a) | a <- as])

numeric :: JsonVal p => (a -> Scientific) -> (Scientific -> Maybe a) -> p a a
numeric f g = prism' f g ?< jsonNumber

tagged :: JsonVal p => Text -> (forall q. JsonVal q => q a b) -> p a b
tagged k p = jsonObject (jsonKeyVal k p)

field
  :: JsonObj p
  => Text -> (forall q. JsonVal q => q a a) -> (s -> a) -> p s a
field k p f = lmap f (jsonKeyVal k p)

tupleElem :: (JsonTup p, Json a) => (s -> a) -> p s a
tupleElem f = lmap f (jsonVal json)

boundedScientific :: Scientific -> Maybe Scientific
boundedScientific s = s <$ guard (abs (base10Exponent s) <= 1024)

integerScientific :: Scientific -> Maybe Integer
integerScientific =
  boundedScientific >=> either (const Nothing) Just . floatingOrInteger @Double

naturalScientific :: Scientific -> Maybe Natural
naturalScientific s = do
  i <- integerScientific s
  fromInteger i <$ guard (i >= 0)

jsonBounded :: (Integral a, Bounded a, JsonVal p) => p a a
jsonBounded = numeric fromIntegral toBoundedInteger

jsonRealFloat :: (RealFloat a, JsonVal p) => p a a -> p a a
jsonRealFloat finite = foldr1 altP
  [ nearly (0/0) isNaN >? jsonNull
  , only (1/0) >? "+inf"
  , only (negate 1/0) >? "-inf"
  , finite
  ]

jsonIntBounded :: forall a p. (Integral a, Bounded a, JsonVal p) => p a a
jsonIntBounded = prism' fromIntegral narrow ?< jsonInt
  where
    narrow i = fromIntegral i <$ guard (lower <= i && i <= upper)
    lower = fromIntegral (minBound @a) :: Int
    upper = fromIntegral (maxBound @a) :: Int

jsonRealFrac :: (Fractional a, Real a, JsonVal p) => p a a
jsonRealFrac = numeric realToFrac (fmap realToFrac . boundedScientific)

timeText
  :: JsonString p
  => (a -> Encoding.Encoding' Text) -> (Text -> Either String a) -> p a a
timeText f g = textual
  ( Text.dropAround (== '"') . Text.decodeLatin1 . LByteString.toStrict
  . Encoding.encodingToLazyByteString . f )
  (either (const Nothing) Just . g)

charText :: JsonString p => p Char Char
charText = textual Text.singleton $ \t -> case Text.uncons t of
  Just (c, rest) | Text.null rest -> Just c
  _ -> Nothing

stringText :: JsonString p => p String String
stringText = iso Text.pack Text.unpack >~ jsonString

keyText :: JsonString p => p Key Key
keyText = iso Key.toText Key.fromText >~ jsonString

versionText :: JsonString p => p Version Version
versionText = textual (Text.pack . showVersion) $ \t ->
  listToMaybe [v | (v, "") <- readP_to_S parseVersion (Text.unpack t)]

uuidText :: JsonString p => p UUID UUID
uuidText = textual UUID.toText UUID.fromText

uriText :: JsonString p => p URI URI
uriText = textual
  (\uri -> Text.pack (URI.uriToString id uri ""))
  (URI.parseURI . Text.unpack)

dayOfWeekText :: JsonString p => p DayOfWeek DayOfWeek
dayOfWeekText = textEnum (Text.toLower . Text.pack . show)
  [Monday, Tuesday, Wednesday, Thursday, Friday, Saturday, Sunday]

quarterOfYearText :: JsonString p => p QuarterOfYear QuarterOfYear
quarterOfYearText = textEnum (Text.toLower . Text.pack . show) [Q1, Q2, Q3, Q4]

readScientific :: Text -> Maybe Scientific
readScientific = readMaybe . Text.unpack

-- | `Scientific` map keys, as @aeson@ renders them.
scientificText :: JsonString p => p Scientific Scientific
scientificText = textual render readScientific
  where
    render s
      | e < 0 || e > 1024 = Text.pack (formatScientific Generic Nothing s)
      | otherwise = Text.pack (show (coefficient s * 10 ^ e))
      where
        e = base10Exponent s

-- | Integral map keys, as @aeson@ renders them.
integralText :: (Show a, JsonString p) => (Scientific -> Maybe a) -> p a a
integralText f = textual (Text.pack . show) (readScientific >=> f)

-- | `RealFloat` map keys, as @aeson@ renders them.
realFloatText :: (RealFloat a, Show a, JsonString p) => p a a
realFloatText = textual render parse
  where
    render d
      | isInfinite d = if d > 0 then "+inf" else "-inf"
      | otherwise = Text.pack (show d)
    parse = \case
      "NaN" -> Just (0/0)
      "+inf" -> Just (1/0)
      "-inf" -> Just (negate 1/0)
      t -> toRealFloat <$> readScientific t

-- Json instances

makePrisms ''Value
makePrisms ''These

-- base
instance Json Bool where
  json = jsonBool
  jsonKeyMap = jsonKeyText
    (textEnum (\b -> if b then "true" else "false") [False, True])
instance Json Ordering where
  json = jsonRule (textEnum (Text.pack . show) [LT, EQ, GT])
instance Json () where json = jsonTuple (pure ())
instance Json Void where
  json = zeroP
  jsonKeyMap = jsonKeyText (textual absurd (const Nothing))
instance Json Char where
  json = jsonRule charText
  jsonList = stringText
  jsonKeyMap = jsonKeyText charText
  jsonKeyListMap = jsonKeyText stringText
instance Json a => Json [a] where
  json = jsonList
  jsonKeyMap = jsonKeyListMap @a
instance Json a => Json (Maybe a) where
  json = eotMaybe . swapped >~ jsonNull >+< json
instance (Json a, Json b) => Json (Either a b) where
  json = tagged "Left" json >+< tagged "Right" json
instance Json Double where
  json = jsonRule (jsonRealFloat jsonDouble)
  jsonKeyMap = jsonKeyText realFloatText
instance Json Float where
  json = jsonRule (jsonRealFloat (numeric fromFloatDigits (Just . toRealFloat)))
  jsonKeyMap = jsonKeyText realFloatText
instance (Integral a, Json a) => Json (Ratio a) where
  json = prism'
    (\r -> (numerator r, denominator r))
    (\(n, d) -> n % d <$ guard (d /= 0))
    ?< jsonObject ((,)
      <$> field "numerator" json fst
      <*> field "denominator" json snd)
instance HasResolution a => Json (Fixed a) where
  json = jsonRealFrac
  jsonKeyMap = jsonKeyText (iso realToFrac realToFrac >~ scientificText)
instance Json Int where
  json = jsonRule jsonInt
  jsonKeyMap = jsonKeyText (integralText toBoundedInteger)
instance Json Int8 where
  json = jsonRule jsonIntBounded
  jsonKeyMap = jsonKeyText (integralText toBoundedInteger)
instance Json Int16 where
  json = jsonRule jsonIntBounded
  jsonKeyMap = jsonKeyText (integralText toBoundedInteger)
instance Json Int32 where
  json = jsonRule jsonIntBounded
  jsonKeyMap = jsonKeyText (integralText toBoundedInteger)
instance Json Int64 where
  json = jsonRule jsonBounded
  jsonKeyMap = jsonKeyText (integralText toBoundedInteger)
instance Json Word where
  json = jsonRule jsonBounded
  jsonKeyMap = jsonKeyText (integralText toBoundedInteger)
instance Json Word8 where
  json = jsonRule jsonIntBounded
  jsonKeyMap = jsonKeyText (integralText toBoundedInteger)
instance Json Word16 where
  json = jsonRule jsonIntBounded
  jsonKeyMap = jsonKeyText (integralText toBoundedInteger)
instance Json Word32 where
  json = jsonRule jsonBounded
  jsonKeyMap = jsonKeyText (integralText toBoundedInteger)
instance Json Word64 where
  json = jsonRule jsonBounded
  jsonKeyMap = jsonKeyText (integralText toBoundedInteger)
instance Json Integer where
  json = jsonRule (numeric fromInteger integerScientific)
  jsonKeyMap = jsonKeyText (integralText integerScientific)
instance Json Natural where
  json = jsonRule (numeric fromIntegral naturalScientific)
  jsonKeyMap = jsonKeyText (integralText naturalScientific)
instance Json CTime where json = coerced >~ json @Int64
instance Json Version where
  json = jsonRule versionText
  jsonKeyMap = jsonKeyText versionText
instance Json a => Json (NonEmpty a) where
  json = prism' toList nonEmpty ?< jsonArray json
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
  json = jsonTuple $ Functor.Pair
    <$> tupleElem (\(Functor.Pair x _) -> x)
    <*> tupleElem (\(Functor.Pair _ y) -> y)
instance (Json (f a), Json (g a)) => Json (Functor.Sum f g a) where
  json = iso
    (\case Functor.InL x -> Left x; Functor.InR y -> Right y)
    (either Functor.InL Functor.InR)
    >~ tagged "InL" json >+< tagged "InR" json
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
      jsonRule @a (dimap (GHC.unM1 . GHC.from) (GHC.to . GHC.M1) gsum)

-- tuples
instance (Json a, Json b) => Json (a, b) where
  json = jsonTuple $ (,)
    <$> tupleElem (view _1) <*> tupleElem (view _2)
instance (Json a, Json b, Json c) => Json (a, b, c) where
  json = jsonTuple $ (,,)
    <$> tupleElem (view _1) <*> tupleElem (view _2) <*> tupleElem (view _3)
instance (Json a, Json b, Json c, Json d) => Json (a, b, c, d) where
  json = jsonTuple $ (,,,)
    <$> tupleElem (view _1) <*> tupleElem (view _2) <*> tupleElem (view _3)
    <*> tupleElem (view _4)
instance (Json a, Json b, Json c, Json d, Json e) => Json (a, b, c, d, e) where
  json = jsonTuple $ (,,,,)
    <$> tupleElem (view _1) <*> tupleElem (view _2) <*> tupleElem (view _3)
    <*> tupleElem (view _4) <*> tupleElem (view _5)
instance (Json a, Json b, Json c, Json d, Json e, Json f)
  => Json (a, b, c, d, e, f) where
  json = jsonTuple $ (,,,,,)
    <$> tupleElem (view _1) <*> tupleElem (view _2) <*> tupleElem (view _3)
    <*> tupleElem (view _4) <*> tupleElem (view _5) <*> tupleElem (view _6)
instance (Json a, Json b, Json c, Json d, Json e, Json f, Json g)
  => Json (a, b, c, d, e, f, g) where
  json = jsonTuple $ (,,,,,,)
    <$> tupleElem (view _1) <*> tupleElem (view _2) <*> tupleElem (view _3)
    <*> tupleElem (view _4) <*> tupleElem (view _5) <*> tupleElem (view _6)
    <*> tupleElem (view _7)
instance (Json a, Json b, Json c, Json d, Json e, Json f, Json g, Json h)
  => Json (a, b, c, d, e, f, g, h) where
  json = jsonTuple $ (,,,,,,,)
    <$> tupleElem (view _1) <*> tupleElem (view _2) <*> tupleElem (view _3)
    <*> tupleElem (view _4) <*> tupleElem (view _5) <*> tupleElem (view _6)
    <*> tupleElem (view _7) <*> tupleElem (view _8)
instance
  ( Json a, Json b, Json c, Json d, Json e, Json f, Json g, Json h, Json i )
  => Json (a, b, c, d, e, f, g, h, i) where
  json = jsonTuple $ (,,,,,,,,)
    <$> tupleElem (view _1) <*> tupleElem (view _2) <*> tupleElem (view _3)
    <*> tupleElem (view _4) <*> tupleElem (view _5) <*> tupleElem (view _6)
    <*> tupleElem (view _7) <*> tupleElem (view _8) <*> tupleElem (view _9)
instance
  ( Json a, Json b, Json c, Json d, Json e, Json f, Json g, Json h, Json i
  , Json j )
  => Json (a, b, c, d, e, f, g, h, i, j) where
  json = jsonTuple $ (,,,,,,,,,)
    <$> tupleElem (view _1) <*> tupleElem (view _2) <*> tupleElem (view _3)
    <*> tupleElem (view _4) <*> tupleElem (view _5) <*> tupleElem (view _6)
    <*> tupleElem (view _7) <*> tupleElem (view _8) <*> tupleElem (view _9)
    <*> tupleElem (view _10)
instance
  ( Json a, Json b, Json c, Json d, Json e, Json f, Json g, Json h, Json i
  , Json j, Json k )
  => Json (a, b, c, d, e, f, g, h, i, j, k) where
  json = jsonTuple $ (,,,,,,,,,,)
    <$> tupleElem (view _1) <*> tupleElem (view _2) <*> tupleElem (view _3)
    <*> tupleElem (view _4) <*> tupleElem (view _5) <*> tupleElem (view _6)
    <*> tupleElem (view _7) <*> tupleElem (view _8) <*> tupleElem (view _9)
    <*> tupleElem (view _10) <*> tupleElem (view _11)
instance
  ( Json a, Json b, Json c, Json d, Json e, Json f, Json g, Json h, Json i
  , Json j, Json k, Json l )
  => Json (a, b, c, d, e, f, g, h, i, j, k, l) where
  json = jsonTuple $ (,,,,,,,,,,,)
    <$> tupleElem (view _1) <*> tupleElem (view _2) <*> tupleElem (view _3)
    <*> tupleElem (view _4) <*> tupleElem (view _5) <*> tupleElem (view _6)
    <*> tupleElem (view _7) <*> tupleElem (view _8) <*> tupleElem (view _9)
    <*> tupleElem (view _10) <*> tupleElem (view _11) <*> tupleElem (view _12)
instance
  ( Json a, Json b, Json c, Json d, Json e, Json f, Json g, Json h, Json i
  , Json j, Json k, Json l, Json m )
  => Json (a, b, c, d, e, f, g, h, i, j, k, l, m) where
  json = jsonTuple $ (,,,,,,,,,,,,)
    <$> tupleElem (view _1) <*> tupleElem (view _2) <*> tupleElem (view _3)
    <*> tupleElem (view _4) <*> tupleElem (view _5) <*> tupleElem (view _6)
    <*> tupleElem (view _7) <*> tupleElem (view _8) <*> tupleElem (view _9)
    <*> tupleElem (view _10) <*> tupleElem (view _11) <*> tupleElem (view _12)
    <*> tupleElem (view _13)
instance
  ( Json a, Json b, Json c, Json d, Json e, Json f, Json g, Json h, Json i
  , Json j, Json k, Json l, Json m, Json n )
  => Json (a, b, c, d, e, f, g, h, i, j, k, l, m, n) where
  json = jsonTuple $ (,,,,,,,,,,,,,)
    <$> tupleElem (view _1) <*> tupleElem (view _2) <*> tupleElem (view _3)
    <*> tupleElem (view _4) <*> tupleElem (view _5) <*> tupleElem (view _6)
    <*> tupleElem (view _7) <*> tupleElem (view _8) <*> tupleElem (view _9)
    <*> tupleElem (view _10) <*> tupleElem (view _11) <*> tupleElem (view _12)
    <*> tupleElem (view _13) <*> tupleElem (view _14)
instance
  ( Json a, Json b, Json c, Json d, Json e, Json f, Json g, Json h, Json i
  , Json j, Json k, Json l, Json m, Json n, Json o )
  => Json (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o) where
  json = jsonTuple $ (,,,,,,,,,,,,,,)
    <$> tupleElem (view _1) <*> tupleElem (view _2) <*> tupleElem (view _3)
    <*> tupleElem (view _4) <*> tupleElem (view _5) <*> tupleElem (view _6)
    <*> tupleElem (view _7) <*> tupleElem (view _8) <*> tupleElem (view _9)
    <*> tupleElem (view _10) <*> tupleElem (view _11) <*> tupleElem (view _12)
    <*> tupleElem (view _13) <*> tupleElem (view _14) <*> tupleElem (view _15)

-- text
instance Json Text where
  json = jsonString
  jsonKeyMap = jsonKeyText jsonString
instance Json LText.Text where
  json = iso LText.toStrict LText.fromStrict >~ jsonString
  jsonKeyMap = jsonKeyText (iso LText.toStrict LText.fromStrict >~ jsonString)
instance Json ShortText where
  json = iso ShortText.toText ShortText.fromText >~ jsonString
  jsonKeyMap =
    jsonKeyText (iso ShortText.toText ShortText.fromText >~ jsonString)

-- scientific
instance Json Scientific where
  json = jsonNumber
  jsonKeyMap = jsonKeyText scientificText

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
  json = jsonRule
    (jsonTuple (Node <$> tupleElem rootLabel <*> tupleElem subForest))

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
  json = keyText
  jsonKeyMap = jsonKeyText keyText
instance Json v => Json (KeyMap v) where
  json = iso KeyMap.toList KeyMap.fromList >~ jsonKeyMap @Key
instance Json Value where
  json = jsonRule $ foldr1 altP
    [ _Null >? jsonNull
    , _Bool >? jsonBool
    , _Number >? jsonNumber
    , _String >? jsonString
    , _Array . iso Vector.toList Vector.fromList >? jsonArray json
    , _Object . iso KeyMap.toList KeyMap.fromList >? jsonDict keyText json
    ]
instance Json DotNetTime where
  json = jsonRule (textual render parse)
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
  json = jsonRule (timeText Encoding.day TimeText.parseDay)
  jsonKeyMap = jsonKeyText (timeText Encoding.day TimeText.parseDay)
instance Json Month where
  json = jsonRule (timeText Encoding.month TimeText.parseMonth)
  jsonKeyMap = jsonKeyText (timeText Encoding.month TimeText.parseMonth)
instance Json Quarter where
  json = jsonRule (timeText Encoding.quarter TimeText.parseQuarter)
  jsonKeyMap = jsonKeyText (timeText Encoding.quarter TimeText.parseQuarter)
instance Json TimeOfDay where
  json = jsonRule (timeText Encoding.timeOfDay TimeText.parseTimeOfDay)
  jsonKeyMap = jsonKeyText (timeText Encoding.timeOfDay TimeText.parseTimeOfDay)
instance Json LocalTime where
  json = jsonRule (timeText Encoding.localTime TimeText.parseLocalTime)
  jsonKeyMap = jsonKeyText (timeText Encoding.localTime TimeText.parseLocalTime)
instance Json ZonedTime where
  json = jsonRule (timeText Encoding.zonedTime TimeText.parseZonedTime)
  jsonKeyMap = jsonKeyText (timeText Encoding.zonedTime TimeText.parseZonedTime)
instance Json UTCTime where
  json = jsonRule (timeText Encoding.utcTime TimeText.parseUTCTime)
  jsonKeyMap = jsonKeyText (timeText Encoding.utcTime TimeText.parseUTCTime)
instance Json NominalDiffTime where json = jsonRule jsonRealFrac
instance Json DiffTime where json = jsonRule jsonRealFrac
instance Json SystemTime where
  json = jsonRule (numeric render parse)
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
  json = jsonObject $ CalendarDiffTime
    <$> field "months" json ctMonths
    <*> field "time" json ctTime
instance Json CalendarDiffDays where
  json = jsonObject $ CalendarDiffDays
    <$> field "months" json cdMonths
    <*> field "days" json cdDays
instance Json DayOfWeek where
  json = jsonRule dayOfWeekText
  jsonKeyMap = jsonKeyText dayOfWeekText
instance Json QuarterOfYear where
  json = jsonRule quarterOfYearText
  jsonKeyMap = jsonKeyText quarterOfYearText

-- uuid-types
instance Json UUID where
  json = jsonRule uuidText
  jsonKeyMap = jsonKeyText uuidText

-- network-uri
instance Json URI where
  json = jsonRule uriText
  jsonKeyMap = jsonKeyText uriText

-- data-fix
instance (Typeable f, Json (f (Fix f))) => Json (Fix f) where
  json = jsonRule @(Fix f) (iso unFix Fix >~ json)
instance (Functor f, Typeable f, Json (f (Fix f))) => Json (Mu f) where
  json = iso (foldMu Fix) (unfoldMu unFix) >~ json @(Fix f)
instance (Functor f, Typeable f, Json (f (Fix f))) => Json (Nu f) where
  json = iso (foldNu Fix) (unfoldNu unFix) >~ json @(Fix f)

-- tagged
instance Json b => Json (Tagged a b) where
  json = coerced >~ json @b
  jsonKeyMap = keysCoerced >~ jsonKeyMap @b
  jsonKeyListMap = keysCoerced >~ jsonKeyListMap @b

-- these
instance (Json a, Json b) => Json (These a b) where
  json = foldr1 altP
    [ _These >? jsonObject
        ((,) <$> field "This" json fst <*> field "That" json snd)
    , _This >? tagged "This" json
    , _That >? tagged "That" json
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
  | otherwise = gtagged

class GSum f where
  gconCount :: Int
  gsingle :: JsonVal p => p (f x) (f x)
  -- | Constructor names, when all constructors are nullary.
  genum :: JsonVal p => Maybe (p (f x) (f x))
  gtagged :: JsonVal p => p (f x) (f x)

instance (GSum f, GSum g) => GSum (f GHC.:+: g) where
  gconCount = gconCount @f + gconCount @g
  gsingle = sumIso >~ gsingle >+< gsingle
  genum = liftA2 (\l r -> sumIso >~ l >+< r) genum genum
  gtagged = sumIso >~ gtagged >+< gtagged

sumIso :: Iso' ((f GHC.:+: g) x) (Either (f x) (g x))
sumIso = iso
  (\case GHC.L1 a -> Left a; GHC.R1 b -> Right b)
  (either GHC.L1 GHC.R1)

instance (GHC.Constructor c, GFields f, GContents f, GNullary f)
  => GSum (GHC.C1 c f) where
    gconCount = 1
    gsingle = dimap GHC.unM1 GHC.M1 $
      if GHC.conIsRecord (undefined :: GHC.C1 c f ())
      then jsonObject gfields else gcontents
    genum = gnullary @f <&> \v ->
      dimap (const ()) (const (GHC.M1 v)) (fromString (gconName @c))
    gtagged = dimap GHC.unM1 GHC.M1 (jsonObject (tag >* contents))
      where
        tag :: JsonObj q => q () ()
        tag = jsonKeyVal "tag" (fromString (gconName @c))
        contents :: JsonObj q => q (f x) (f x)
        contents
          | GHC.conIsRecord (undefined :: GHC.C1 c f ()) = gfields
          | Just v <- gnullary @f = dimap (const ()) (const v) oneP
          | otherwise = jsonKeyVal "contents" gcontents

gconName :: forall (c :: GHC.Meta). GHC.Constructor c => String
gconName = GHC.conName (undefined :: GHC.C1 c GHC.U1 ())

gselName :: forall (s :: GHC.Meta). GHC.Selector s => String
gselName = GHC.selName (undefined :: GHC.S1 s GHC.U1 ())

class GFields f where
  gfields :: JsonObj p => p (f x) (f x)
instance (GHC.Selector s, Json a) => GFields (GHC.S1 s (GHC.K1 i a)) where
  gfields = dimap (GHC.unK1 . GHC.unM1) (GHC.M1 . GHC.K1) $
    jsonKeyVal (Text.pack (gselName @s)) json
instance (GFields f, GFields g) => GFields (f GHC.:*: g) where
  gfields = productIso >~ gfields >*< gfields
instance GFields GHC.U1 where
  gfields = dimap (const ()) (const GHC.U1) oneP

class GElements f where
  gelements :: JsonTup p => p (f x) (f x)
instance Json a => GElements (GHC.S1 s (GHC.K1 i a)) where
  gelements = dimap (GHC.unK1 . GHC.unM1) (GHC.M1 . GHC.K1) (jsonVal json)
instance (GElements f, GElements g) => GElements (f GHC.:*: g) where
  gelements = productIso >~ gelements >*< gelements
instance GElements GHC.U1 where
  gelements = dimap (const ()) (const GHC.U1) oneP

productIso :: Iso' ((f GHC.:*: g) x) (f x, g x)
productIso = iso (\(a GHC.:*: b) -> (a, b)) (uncurry (GHC.:*:))

class GContents f where
  gcontents :: JsonVal p => p (f x) (f x)
instance Json a => GContents (GHC.S1 s (GHC.K1 i a)) where
  gcontents = dimap (GHC.unK1 . GHC.unM1) (GHC.M1 . GHC.K1) json
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
