{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RequiredTypeArguments #-}

module Control.Lens.Grammar.Json
  ( -- * Json
    Json (..)
  , JsonVal (..)
  , JsonString (..)
  , JsonTup (..)
  , JsonObj (..)
  , jsonListOf
  , TextMap (..)
    -- * Aeson
  , jsonParse
  , jsonPrint
    -- * TypeScript
  , TsType (..)
  , TsGrammor (..)
  , jsonType
    -- * Generics
  , GJson (..)
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.Grammar
import Control.Monad
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State.Strict
import Data.Aeson.Encoding qualified as Encoding
import Data.Aeson.Key (Key)
import Data.Aeson.Key qualified as Key
import Data.Aeson.KeyMap (KeyMap)
import Data.Aeson.KeyMap qualified as KeyMap
import Data.Aeson.Types
  (DotNetTime (..), JSONPathElement (..), Object, Parser, Value (..), (<?>))
import Data.Aeson.Types qualified as Aeson
import Data.Bifunctor.Joker
import Data.ByteString.Lazy qualified as LByteString
import Data.Coerce
import Data.DList (DList)
import Data.DList qualified as DList
import Data.DList.DNonEmpty (DNonEmpty)
import Data.DList.DNonEmpty qualified as DNonEmpty
import Data.Fix (Fix (..), Mu, Nu, foldMu, foldNu, unfoldMu, unfoldNu)
import Data.Fixed (Fixed, HasResolution (..), Nano)
import Data.Foldable (toList)
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
import Data.List.NonEmpty (NonEmpty, nonEmpty)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe
import Data.Monoid (Alt (..), Ap (..))
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
import Data.Text.Lens (IsText (..))
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
import Data.Tree (Tree (..))
import Data.Tuple (Solo (MkSolo), getSolo)
import Data.Typeable (Typeable, typeRep)
import Data.UUID.Types (UUID)
import Data.UUID.Types qualified as UUID
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Data.Vector.Generic qualified as VG
import Data.Vector.Primitive qualified as VP
import Data.Vector.Storable qualified as VS
import Data.Vector.Unboxed qualified as VU
import Data.Version (Version, parseVersion, showVersion)
import Data.Void (Void)
import Data.Word (Word8, Word16, Word32, Word64)
import Foreign.C.Types (CTime (..))
import Foreign.Storable (Storable)
import GHC.Exts qualified as Exts
import GHC.Generics qualified as GHC
import Network.URI (URI)
import Network.URI qualified as URI
import Numeric.Natural (Natural)
import Text.ParserCombinators.ReadP (readP_to_S)

{- | `Json` grammars, compatible with @aeson@'s
@ToJSON@ & @FromJSON@ instances.
`jsonList` mirrors @aeson@'s @toJSONList@,
so that `String`s are JSON strings rather than arrays.
-}
class Json a where
  json :: JsonVal p => p a a
  default json
    :: (GHC.Generic a, GJson (GHC.Rep a), Typeable a, JsonVal p) => p a a
  json = jsonGeneric
  jsonList :: JsonVal p => p [a] [a]
  jsonList = jsonListOf json

{- | A `GHC.Generic` `Json` grammar, defined as a `rule`
named by its `Typeable` type, so that each instantiation of
a parametric type is its own (possibly recursive) definition.
-}
jsonGeneric
  :: forall a p. (GHC.Generic a, GJson (GHC.Rep a), Typeable a, JsonVal p)
  => p a a
jsonGeneric = jsonRule @a (iso GHC.from GHC.to >~ gjson)

-- | A `rule` named by a `Typeable` type.
jsonRule :: forall a p. (Typeable a, JsonVal p) => p a a -> p a a
jsonRule = rule (show (typeRep (Proxy @a)))

jsonListOf :: JsonVal p => p a b -> p [a] [b]
jsonListOf p = iso Vector.fromList Vector.toList >~ jsonArray p

class
  ( CocartesianChoice p
  , JsonString p
  , forall x y. BackusNaurForm (p x y)
  ) => JsonVal p where
  jsonNull :: p () ()
  jsonBool :: p Bool Bool
  jsonNumber :: p Scientific Scientific
  jsonArray :: p a b -> p (Vector a) (Vector b)
  jsonDict
    :: (forall q. JsonString q => q a b)
    -> p c d -> p [(a, c)] [(b, d)]
  jsonTuple :: (forall q. JsonTup q => q a b) -> p a b
  jsonObject :: (forall q. JsonObj q => q a b) -> p a b

{- | `JsonString`s have string literals, exactly matching some text.
They're determined by `Cochoice` partiality.

prop> fromString s = only (Text.pack s) ?< jsonString
-}
class
  ( Choice p, Cochoice p
  , forall x y. (x ~ (), y ~ ()) => IsString (p x y)
  ) => JsonString p where
  jsonString :: p Text Text

{- | A `Map` with textual keys, encoded as a JSON object,
whereas a `Map` is encoded as a JSON array of key-value pairs.
-}
newtype TextMap str val = TextMap {runTextMap :: Map str val}
  deriving stock (Eq, Ord, Show, Read)

class Monoidal p => JsonTup p where
  jsonVal :: (forall q. JsonVal q => q a b) -> p a b

class Monoidal p => JsonObj p where
  jsonKeyVal :: Text -> (forall q. JsonVal q => q a b) -> p a b

class GJson f where
  gjson :: JsonVal p => p (f a) (f a)

-- Aeson --

jsonParse :: Json a => Value -> Parser a
jsonParse = runJsonParsor json

jsonPrint :: Json a => a -> Maybe Value
jsonPrint = runJsonPrintor json

newtype JsonParsor a b = JsonParsor {runJsonParsor :: Value -> Parser b}
newtype JsonPrintor a b = JsonPrintor {runJsonPrintor :: a -> Maybe Value}
newtype TupParsor a b = TupParsor {runTupParsor :: StateT [Value] Parser b}
newtype TupPrintor a b = TupPrintor {runTupPrintor :: a -> Maybe [Value]}
newtype ObjParsor a b = ObjParsor {runObjParsor :: Object -> Parser b}
newtype ObjPrintor a b = ObjPrintor {runObjPrintor :: a -> Maybe Object}

-- TypeScript --

data TsType
  = TsNonTerminal String -- ^ @T@
  | TsNull -- ^ @null@
  | TsBoolean -- ^ @boolean@
  | TsNumber -- ^ @number@
  | TsString -- ^ @string@
  | TsArray TsType -- ^ T[]
  | TsDict TsType -- ^ @{[key: string]: T}@
  | TsTuple [TsType] -- ^ @[T,U]@
  | TsObject [(Text, TsType)] -- ^ @{abc : T, xyz : U}@
  | TsNever -- ^ @never@
  | TsUnion TsType TsType -- ^ @T | U@
  deriving stock (Eq, Ord, Show, Read)

{- | `TsGrammor` interprets `Json` grammars as TypeScript type definitions.
Each `rule` is a named type definition. Its argument is the set of
names of the rules being defined, so that a recursive occurrence
of a rule is just its `TsNonTerminal` name.
-}
newtype TsGrammor a b = TsGrammor
  {runTsGrammor :: Set String -> Bnf TsType TsType}

jsonType :: forall a. Json a => Bnf TsType TsType
jsonType = runTsGrammor (json @a) Set.empty

tsOr :: TsType -> TsType -> TsType
tsOr t0 t1
  | t0 == t1 = t0
  | t0 == TsNever = t1
  | t1 == TsNever = t0
  | otherwise = TsUnion t0 t1

-- JsonParsor instances
deriving via ReaderT Value Parser instance Functor (JsonParsor a)
deriving via Joker (ReaderT Value Parser) instance Profunctor JsonParsor
deriving via Joker (ReaderT Value Parser) instance Choice JsonParsor
deriving via Joker (ReaderT Value Parser)
  instance CocartesianMonoidal JsonParsor
deriving via Joker (ReaderT Value Parser)
  instance CocartesianChoice JsonParsor
instance Cochoice JsonParsor where
  unleft (JsonParsor p) = JsonParsor $ \v ->
    p v >>= either pure (\_ -> fail "unleft: unexpected Right")
  unright (JsonParsor p) = JsonParsor $ \v ->
    p v >>= either (\_ -> fail "unright: unexpected Left") pure
instance BackusNaurForm (JsonParsor a b)
instance (x ~ (), y ~ ()) => IsString (JsonParsor x y) where
  fromString s = JsonParsor $ Aeson.withText (show s) $ \t ->
    if t == Text.pack s then pure () else fail ("expected " <> show s)
instance JsonString JsonParsor where
  jsonString = JsonParsor (Aeson.withText "string" pure)
instance JsonVal JsonParsor where
  jsonNull = JsonParsor $ \case
    Null -> pure ()
    v -> Aeson.typeMismatch "null" v
  jsonBool = JsonParsor (Aeson.withBool "boolean" pure)
  jsonNumber = JsonParsor (Aeson.withScientific "number" pure)
  jsonArray (JsonParsor p) = JsonParsor $ Aeson.withArray "array" $
    Vector.imapM (\i v -> p v <?> Index i)
  jsonDict key (JsonParsor p) = JsonParsor $ Aeson.withObject "dict" $
    traverse
      (\(k,v) -> (,)
        <$> runJsonParsor key (String (Key.toText k))
        <*> p v <?> Key k)
      . KeyMap.toList
  jsonTuple tup = JsonParsor $ Aeson.withArray "tuple" $ \arr ->
    runStateT (runTupParsor tup) (Vector.toList arr) >>= \case
      (b, []) -> pure b
      _ -> fail "tuple too long"
  jsonObject obj = JsonParsor $ Aeson.withObject "object" (runObjParsor obj)

-- JsonPrintor instances
deriving via Forget (Alt Maybe Value) a instance Functor (JsonPrintor a)
deriving via Forget (Alt Maybe Value) instance Profunctor JsonPrintor
deriving via Forget (Alt Maybe Value) instance Choice JsonPrintor
deriving via Forget (Alt Maybe Value) instance Cochoice JsonPrintor
deriving via Forget (Alt Maybe Value)
  instance CocartesianMonoidal JsonPrintor
instance CocartesianChoice JsonPrintor where
  emptyP = JsonPrintor (const Nothing)
  altP (JsonPrintor p) (JsonPrintor q) = JsonPrintor $ \a -> p a <|> q a
instance BackusNaurForm (JsonPrintor a b)
instance (x ~ (), y ~ ()) => IsString (JsonPrintor x y) where
  fromString s = JsonPrintor (const (Just (String (Text.pack s))))
instance JsonString JsonPrintor where
  jsonString = JsonPrintor (Just . String)
instance JsonVal JsonPrintor where
  jsonNull = JsonPrintor (const (Just Null))
  jsonBool = JsonPrintor (Just . Bool)
  jsonNumber = JsonPrintor (Just . Number)
  jsonArray (JsonPrintor p) = JsonPrintor (fmap Array . traverse p)
  jsonDict key (JsonPrintor p) = JsonPrintor $
    fmap (Object . KeyMap.fromList) . traverse
      (\(a,c) -> (,) <$> printKey a <*> p c)
    where
      printKey a = runJsonPrintor key a >>= \case
        String t -> Just (Key.fromText t)
        _ -> Nothing
  jsonTuple tup = JsonPrintor (fmap (Array . Vector.fromList) . runTupPrintor tup)
  jsonObject obj = JsonPrintor (fmap Object . runObjPrintor obj)

-- TupParsor & TupPrintor instances
deriving via StateT [Value] Parser instance Functor (TupParsor a)
deriving via StateT [Value] Parser instance Applicative (TupParsor a)
deriving via Joker (StateT [Value] Parser) instance Profunctor TupParsor
instance JsonTup TupParsor where
  jsonVal p = TupParsor $ StateT $ \case
    [] -> fail "tuple too short"
    v:vs -> (, vs) <$> runJsonParsor p v
deriving via Forget (Ap Maybe [Value]) a instance Functor (TupPrintor a)
deriving via Forget (Ap Maybe [Value]) a instance Applicative (TupPrintor a)
deriving via Forget (Ap Maybe [Value]) instance Profunctor TupPrintor
instance JsonTup TupPrintor where
  jsonVal p = TupPrintor (fmap pure . runJsonPrintor p)

-- ObjParsor & ObjPrintor instances
deriving via ReaderT Object Parser instance Functor (ObjParsor a)
deriving via ReaderT Object Parser instance Applicative (ObjParsor a)
deriving via Joker (ReaderT Object Parser) instance Profunctor ObjParsor
instance JsonObj ObjParsor where
  jsonKeyVal k p = ObjParsor $ \o -> case KeyMap.lookup key o of
    Nothing -> fail ("missing key " <> show k)
    Just v -> runJsonParsor p v <?> Key key
    where
      key = Key.fromText k
deriving via Forget (Ap Maybe Object) a instance Functor (ObjPrintor a)
deriving via Forget (Ap Maybe Object) a instance Applicative (ObjPrintor a)
deriving via Forget (Ap Maybe Object) instance Profunctor ObjPrintor
instance JsonObj ObjPrintor where
  jsonKeyVal k p = ObjPrintor $
    fmap (KeyMap.singleton (Key.fromText k)) . runJsonPrintor p

-- TsGrammor instances
instance NonTerminalSymbol TsType where nonTerminal = TsNonTerminal
deriving via Grammor (Set String -> Bnf TsType TsType) a
  instance Functor (TsGrammor a)
deriving via Grammor (Set String -> Bnf TsType TsType)
  instance Profunctor TsGrammor
deriving via Grammor (Set String -> Bnf TsType TsType)
  instance Choice TsGrammor
instance Cochoice TsGrammor where
  unleft = coerce
  unright = coerce
instance CocartesianMonoidal TsGrammor where
  zeroP = tsType TsNever
  TsGrammor b0 >+< TsGrammor b1 = TsGrammor (liftA2 (liftA2 tsOr) b0 b1)
instance CocartesianChoice TsGrammor where
  emptyP = tsType TsNever
  altP (TsGrammor b0) (TsGrammor b1) = TsGrammor (liftA2 (liftA2 tsOr) b0 b1)
instance BackusNaurForm (TsGrammor a b) where
  rule name (TsGrammor body) = TsGrammor $ \defining ->
    if Set.member name defining then nonTerminal name
    else rule name (body (Set.insert name defining))
  ruleRec name f = rule name (f (TsGrammor (\_ -> nonTerminal name)))
instance (x ~ (), y ~ ()) => IsString (TsGrammor x y) where
  fromString _ = tsType TsString
instance JsonString TsGrammor where
  jsonString = tsType TsString
instance JsonVal TsGrammor where
  jsonNull = tsType TsNull
  jsonBool = tsType TsBoolean
  jsonNumber = tsType TsNumber
  jsonArray (TsGrammor b) = TsGrammor (fmap TsArray <$> b)
  jsonDict _ (TsGrammor v) = TsGrammor (fmap TsDict <$> v)
  jsonTuple tup = TsGrammor (fmap TsTuple <$> runGrammor tup)
  jsonObject obj = TsGrammor (fmap TsObject <$> runGrammor obj)
instance JsonTup (Grammor (Set String -> Bnf TsType [TsType])) where
  jsonVal g = Grammor (fmap pure <$> runTsGrammor g)
instance JsonObj (Grammor (Set String -> Bnf TsType [(Text, TsType)])) where
  jsonKeyVal k v = Grammor (fmap (pure . (k,)) <$> runTsGrammor v)

tsType :: TsType -> TsGrammor a b
tsType = TsGrammor . pure . pure

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

jsonRealFloat :: (RealFloat a, JsonVal p) => p a a
jsonRealFloat = foldr1 altP
  [ prism' (const (0/0)) (\d -> () <$ guard (isNaN d)) >? jsonNull
  , only (1/0) >? "+inf"
  , only (negate 1/0) >? "-inf"
  , numeric fromFloatDigits (Just . toRealFloat)
  ]

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

-- Json instances

-- base
instance Json Bool where json = jsonBool
instance Json Ordering where json = textEnum (Text.pack . show) [LT, EQ, GT]
instance Json () where json = jsonTuple (pure ())
instance Json Void where json = zeroP
instance Json Char where
  json = charText
  jsonList = stringText
instance Json a => Json [a] where json = jsonList
instance Json a => Json (Maybe a) where
  json = iso (maybe (Left ()) Right) (either (const Nothing) Just)
    >~ jsonNull >+< json
instance (Json a, Json b) => Json (Either a b) where
  json = tagged "Left" json >+< tagged "Right" json
instance Json Double where json = jsonRealFloat
instance Json Float where json = jsonRealFloat
instance (Integral a, Json a) => Json (Ratio a) where
  json = prism'
    (\r -> (numerator r, denominator r))
    (\(n, d) -> n % d <$ guard (d /= 0))
    ?< jsonObject ((,) <$> field "numerator" json fst <*> field "denominator" json snd)
instance HasResolution a => Json (Fixed a) where json = jsonRealFrac
instance Json Int where json = jsonBounded
instance Json Int8 where json = jsonBounded
instance Json Int16 where json = jsonBounded
instance Json Int32 where json = jsonBounded
instance Json Int64 where json = jsonBounded
instance Json Word where json = jsonBounded
instance Json Word8 where json = jsonBounded
instance Json Word16 where json = jsonBounded
instance Json Word32 where json = jsonBounded
instance Json Word64 where json = jsonBounded
instance Json Integer where json = numeric fromInteger integerScientific
instance Json Natural where json = numeric fromIntegral naturalScientific
instance Json CTime where json = coerced >~ json @Int64
instance Json Version where json = versionText
instance Json a => Json (NonEmpty a) where
  json = prism' toList nonEmpty ?< jsonListOf json
instance Json a => Json (Solo a) where
  json = iso getSolo MkSolo >~ json @a
  jsonList = iso (map getSolo) (map MkSolo) >~ jsonList @a
instance Json a => Json (Identity a) where
  json = coerced >~ json @a
  jsonList = coerced >~ jsonList @a
instance Json a => Json (Const a b) where json = coerced >~ json @a
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
instance (GHC.Generic a, GJson (GHC.Rep a), Typeable a)
  => Json (GHC.Generically a) where
    json = iso (\(GHC.Generically a) -> a) GHC.Generically >~ jsonGeneric @a

-- tuples
instance (Json a, Json b) => Json (a, b) where
  json = jsonTuple $ (,)
    <$> tupleElem (view _1) <*> tupleElem (view _2)
instance (Json a, Json b, Json c) => Json (a, b, c) where
  json = jsonTuple $ (,,)
    <$> tupleElem (view _1) <*> tupleElem (view _2) <*> tupleElem (view _3)
instance (Json a, Json b, Json c, Json d) => Json (a, b, c, d) where
  json = jsonTuple $ (,,,)
    <$> tupleElem (view _1) <*> tupleElem (view _2) <*> tupleElem (view _3) <*> tupleElem (view _4)
instance (Json a, Json b, Json c, Json d, Json e) => Json (a, b, c, d, e) where
  json = jsonTuple $ (,,,,)
    <$> tupleElem (view _1) <*> tupleElem (view _2) <*> tupleElem (view _3) <*> tupleElem (view _4) <*> tupleElem (view _5)
instance (Json a, Json b, Json c, Json d, Json e, Json f) => Json (a, b, c, d, e, f) where
  json = jsonTuple $ (,,,,,)
    <$> tupleElem (view _1) <*> tupleElem (view _2) <*> tupleElem (view _3) <*> tupleElem (view _4) <*> tupleElem (view _5) <*> tupleElem (view _6)
instance (Json a, Json b, Json c, Json d, Json e, Json f, Json g) => Json (a, b, c, d, e, f, g) where
  json = jsonTuple $ (,,,,,,)
    <$> tupleElem (view _1) <*> tupleElem (view _2) <*> tupleElem (view _3) <*> tupleElem (view _4) <*> tupleElem (view _5) <*> tupleElem (view _6) <*> tupleElem (view _7)
instance (Json a, Json b, Json c, Json d, Json e, Json f, Json g, Json h) => Json (a, b, c, d, e, f, g, h) where
  json = jsonTuple $ (,,,,,,,)
    <$> tupleElem (view _1) <*> tupleElem (view _2) <*> tupleElem (view _3) <*> tupleElem (view _4) <*> tupleElem (view _5) <*> tupleElem (view _6) <*> tupleElem (view _7) <*> tupleElem (view _8)
instance (Json a, Json b, Json c, Json d, Json e, Json f, Json g, Json h, Json i) => Json (a, b, c, d, e, f, g, h, i) where
  json = jsonTuple $ (,,,,,,,,)
    <$> tupleElem (view _1) <*> tupleElem (view _2) <*> tupleElem (view _3) <*> tupleElem (view _4) <*> tupleElem (view _5) <*> tupleElem (view _6) <*> tupleElem (view _7) <*> tupleElem (view _8) <*> tupleElem (view _9)
instance (Json a, Json b, Json c, Json d, Json e, Json f, Json g, Json h, Json i, Json j) => Json (a, b, c, d, e, f, g, h, i, j) where
  json = jsonTuple $ (,,,,,,,,,)
    <$> tupleElem (view _1) <*> tupleElem (view _2) <*> tupleElem (view _3) <*> tupleElem (view _4) <*> tupleElem (view _5) <*> tupleElem (view _6) <*> tupleElem (view _7) <*> tupleElem (view _8) <*> tupleElem (view _9) <*> tupleElem (view _10)
instance (Json a, Json b, Json c, Json d, Json e, Json f, Json g, Json h, Json i, Json j, Json k) => Json (a, b, c, d, e, f, g, h, i, j, k) where
  json = jsonTuple $ (,,,,,,,,,,)
    <$> tupleElem (view _1) <*> tupleElem (view _2) <*> tupleElem (view _3) <*> tupleElem (view _4) <*> tupleElem (view _5) <*> tupleElem (view _6) <*> tupleElem (view _7) <*> tupleElem (view _8) <*> tupleElem (view _9) <*> tupleElem (view _10) <*> tupleElem (view _11)
instance (Json a, Json b, Json c, Json d, Json e, Json f, Json g, Json h, Json i, Json j, Json k, Json l) => Json (a, b, c, d, e, f, g, h, i, j, k, l) where
  json = jsonTuple $ (,,,,,,,,,,,)
    <$> tupleElem (view _1) <*> tupleElem (view _2) <*> tupleElem (view _3) <*> tupleElem (view _4) <*> tupleElem (view _5) <*> tupleElem (view _6) <*> tupleElem (view _7) <*> tupleElem (view _8) <*> tupleElem (view _9) <*> tupleElem (view _10) <*> tupleElem (view _11) <*> tupleElem (view _12)
instance (Json a, Json b, Json c, Json d, Json e, Json f, Json g, Json h, Json i, Json j, Json k, Json l, Json m) => Json (a, b, c, d, e, f, g, h, i, j, k, l, m) where
  json = jsonTuple $ (,,,,,,,,,,,,)
    <$> tupleElem (view _1) <*> tupleElem (view _2) <*> tupleElem (view _3) <*> tupleElem (view _4) <*> tupleElem (view _5) <*> tupleElem (view _6) <*> tupleElem (view _7) <*> tupleElem (view _8) <*> tupleElem (view _9) <*> tupleElem (view _10) <*> tupleElem (view _11) <*> tupleElem (view _12) <*> tupleElem (view _13)
instance (Json a, Json b, Json c, Json d, Json e, Json f, Json g, Json h, Json i, Json j, Json k, Json l, Json m, Json n) => Json (a, b, c, d, e, f, g, h, i, j, k, l, m, n) where
  json = jsonTuple $ (,,,,,,,,,,,,,)
    <$> tupleElem (view _1) <*> tupleElem (view _2) <*> tupleElem (view _3) <*> tupleElem (view _4) <*> tupleElem (view _5) <*> tupleElem (view _6) <*> tupleElem (view _7) <*> tupleElem (view _8) <*> tupleElem (view _9) <*> tupleElem (view _10) <*> tupleElem (view _11) <*> tupleElem (view _12) <*> tupleElem (view _13) <*> tupleElem (view _14)
instance (Json a, Json b, Json c, Json d, Json e, Json f, Json g, Json h, Json i, Json j, Json k, Json l, Json m, Json n, Json o) => Json (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o) where
  json = jsonTuple $ (,,,,,,,,,,,,,,)
    <$> tupleElem (view _1) <*> tupleElem (view _2) <*> tupleElem (view _3) <*> tupleElem (view _4) <*> tupleElem (view _5) <*> tupleElem (view _6) <*> tupleElem (view _7) <*> tupleElem (view _8) <*> tupleElem (view _9) <*> tupleElem (view _10) <*> tupleElem (view _11) <*> tupleElem (view _12) <*> tupleElem (view _13) <*> tupleElem (view _14) <*> tupleElem (view _15)

-- text
instance Json Text where json = jsonString
instance Json LText.Text where
  json = iso LText.toStrict LText.fromStrict >~ jsonString
instance Json ShortText where
  json = iso ShortText.toText ShortText.fromText >~ jsonString

-- scientific
instance Json Scientific where json = jsonNumber

-- containers
instance Json a => Json (Seq a) where
  json = iso toList Seq.fromList >~ jsonListOf json
instance (Ord a, Json a) => Json (Set a) where
  json = iso Set.toList Set.fromList >~ jsonListOf json
instance Json IntSet where
  json = iso IntSet.toList IntSet.fromList >~ json @[Int]
instance Json a => Json (IntMap a) where
  json = iso IntMap.toList IntMap.fromList >~ json @[(Int, a)]
instance (Ord k, Json k, Json v) => Json (Map k v) where
  json = iso Map.toList Map.fromList >~ json @[(k, v)]
instance (Ord str, IsText str, Json val) => Json (TextMap str val) where
  json = iso (Map.toList . runTextMap) (TextMap . Map.fromList)
    >~ jsonDict (from packed . packed >~ jsonString) json
instance (Typeable a, Json a) => Json (Tree a) where
  json = jsonRule @(Tree a) $ jsonTuple $
    Node <$> tupleElem rootLabel <*> tupleElem subForest

-- dlist
instance Json a => Json (DList a) where
  json = iso DList.toList DList.fromList >~ jsonListOf json
instance Json a => Json (DNonEmpty a) where
  json = iso DNonEmpty.toNonEmpty DNonEmpty.fromNonEmpty >~ json @(NonEmpty a)

-- vector
instance Json a => Json (Vector a) where json = jsonArray json
instance (Storable a, Json a) => Json (VS.Vector a) where
  json = iso VG.convert VG.convert >~ jsonArray json
instance (VP.Prim a, Json a) => Json (VP.Vector a) where
  json = iso VG.convert VG.convert >~ jsonArray json
instance (VU.Unbox a, Json a) => Json (VU.Vector a) where
  json = iso VG.convert VG.convert >~ jsonArray json

-- primitive
instance Json a => Json (Array a) where
  json = iso Exts.toList Exts.fromList >~ json @[a]
instance Json a => Json (SmallArray a) where
  json = iso Exts.toList Exts.fromList >~ json @[a]
instance (Prim a, Json a) => Json (PrimArray a) where
  json = iso Exts.toList Exts.fromList >~ json @[a]

-- unordered-containers
instance (Eq a, Hashable a, Json a) => Json (HashSet a) where
  json = iso HashSet.toList HashSet.fromList >~ jsonListOf json
instance (Eq k, Hashable k, Json k, Json v) => Json (HashMap k v) where
  json = iso HashMap.toList HashMap.fromList >~ json @[(k, v)]

-- aeson
instance Json Key where json = keyText
instance Json v => Json (KeyMap v) where
  json = iso KeyMap.toList KeyMap.fromList >~ jsonDict keyText json
instance Json Value where
  json = ruleRec "Value" $ \value -> foldr1 altP
    [ valueCase (const Null) (\case Null -> Just (); _ -> Nothing) jsonNull
    , valueCase Bool (\case Bool b -> Just b; _ -> Nothing) jsonBool
    , valueCase Number (\case Number n -> Just n; _ -> Nothing) jsonNumber
    , valueCase String (\case String t -> Just t; _ -> Nothing) jsonString
    , valueCase Array (\case Array a -> Just a; _ -> Nothing) (jsonArray value)
    , valueCase Object (\case Object o -> Just o; _ -> Nothing)
        (iso KeyMap.toList KeyMap.fromList >~ jsonDict keyText value)
    ]
    where
      valueCase f g p = prism' f g >? p
instance Json DotNetTime where
  json = textual render parse
    where
      render (DotNetTime t) = Text.pack $
        formatTime defaultTimeLocale "/Date(%s" t
        <> take 3 (formatTime defaultTimeLocale "%q" t)
        <> ")/"
      parse t =
        let (s, m) = Text.splitAt (Text.length t - 5) t
        in DotNetTime <$> parseTimeM True defaultTimeLocale
          "/Date(%s%Q)/" (Text.unpack (Text.concat [s, ".", m]))

-- time
instance Json Day where json = timeText Encoding.day TimeText.parseDay
instance Json Month where json = timeText Encoding.month TimeText.parseMonth
instance Json Quarter where
  json = timeText Encoding.quarter TimeText.parseQuarter
instance Json TimeOfDay where
  json = timeText Encoding.timeOfDay TimeText.parseTimeOfDay
instance Json LocalTime where
  json = timeText Encoding.localTime TimeText.parseLocalTime
instance Json ZonedTime where
  json = timeText Encoding.zonedTime TimeText.parseZonedTime
instance Json UTCTime where
  json = timeText Encoding.utcTime TimeText.parseUTCTime
instance Json NominalDiffTime where json = jsonRealFrac
instance Json DiffTime where json = jsonRealFrac
instance Json SystemTime where
  json = numeric render parse
    where
      render (MkSystemTime s ns) =
        realToFrac (fromIntegral s + fromIntegral ns / 1000000000 :: Nano)
      parse sci = do
        n <- realToFrac <$> boundedScientific sci :: Maybe Nano
        let (s, ns) = floor (n * fromInteger (resolution n)) `divMod` resolution n
        Just (MkSystemTime (fromInteger s) (fromInteger ns))
instance Json CalendarDiffTime where
  json = jsonObject $ CalendarDiffTime
    <$> field "months" json ctMonths
    <*> field "time" json ctTime
instance Json CalendarDiffDays where
  json = jsonObject $ CalendarDiffDays
    <$> field "months" json cdMonths
    <*> field "days" json cdDays
instance Json DayOfWeek where json = dayOfWeekText
instance Json QuarterOfYear where json = quarterOfYearText

-- uuid-types
instance Json UUID where json = uuidText

-- network-uri
instance Json URI where json = uriText

-- data-fix
instance (Typeable f, Json (f (Fix f))) => Json (Fix f) where
  json = jsonRule @(Fix f) (iso unFix Fix >~ json)
instance (Functor f, Typeable f, Json (f (Fix f))) => Json (Mu f) where
  json = iso (foldMu Fix) (unfoldMu unFix) >~ json @(Fix f)
instance (Functor f, Typeable f, Json (f (Fix f))) => Json (Nu f) where
  json = iso (foldNu Fix) (unfoldNu unFix) >~ json @(Fix f)

-- tagged
instance Json b => Json (Tagged a b) where json = coerced >~ json @b

-- these
instance (Json a, Json b) => Json (These a b) where
  json = foldr1 altP
    [ prism' (uncurry These) (\case These a b -> Just (a, b); _ -> Nothing)
      >? jsonObject ((,) <$> field "This" json fst <*> field "That" json snd)
    , prism' This (\case This a -> Just a; _ -> Nothing) >? tagged "This" json
    , prism' That (\case That b -> Just b; _ -> Nothing) >? tagged "That" json
    ]
instance (Json (f a), Json (g a)) => Json (These1 f g a) where
  json = foldr1 altP
    [ prism' (uncurry These1) (\case These1 a b -> Just (a, b); _ -> Nothing)
      >? jsonObject ((,) <$> field "This" json fst <*> field "That" json snd)
    , prism' This1 (\case This1 a -> Just a; _ -> Nothing) >? tagged "This" json
    , prism' That1 (\case That1 b -> Just b; _ -> Nothing) >? tagged "That" json
    ]

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

instance GSum f => GJson (GHC.D1 d f) where
  gjson = dimap GHC.unM1 GHC.M1 $
    if gconCount @f == 1 then gsingle
    else if gallNullary @f then gnullaryTag
    else gtagged

class GSum f where
  gconCount :: Int
  gallNullary :: Bool
  gsingle :: JsonVal p => p (f x) (f x)
  gnullaryTag :: JsonVal p => p (f x) (f x)
  gtagged :: JsonVal p => p (f x) (f x)

instance (GSum f, GSum g) => GSum (f GHC.:+: g) where
  gconCount = gconCount @f + gconCount @g
  gallNullary = gallNullary @f && gallNullary @g
  gsingle = sumIso >~ gsingle >+< gsingle
  gnullaryTag = sumIso >~ gnullaryTag >+< gnullaryTag
  gtagged = sumIso >~ gtagged >+< gtagged

sumIso :: Iso ((f GHC.:+: g) x) ((f GHC.:+: g) x) (Either (f x) (g x)) (Either (f x) (g x))
sumIso = iso (\case GHC.L1 a -> Left a; GHC.R1 b -> Right b) (either GHC.L1 GHC.R1)

instance (GHC.Constructor c, GFields f, GContents f, GNullary f)
  => GSum (GHC.C1 c f) where
    gconCount = 1
    gallNullary = isJust (gnullary @f)
    gsingle = dimap GHC.unM1 GHC.M1 $
      if GHC.conIsRecord (undefined :: GHC.C1 c f ()) then jsonObject gfields else gcontents
    gnullaryTag = case gnullary @f of
      Nothing -> error "GJson: impossible"
      Just v -> dimap (const ()) (const (GHC.M1 v)) (fromString (gconName @c))
    gtagged = dimap GHC.unM1 GHC.M1 (jsonObject (tag >* contents))
      where
        tag :: JsonObj q => q () ()
        tag = jsonKeyVal (Text.pack "tag") (fromString (gconName @c))
        contents :: JsonObj q => q (f x) (f x)
        contents
          | GHC.conIsRecord (undefined :: GHC.C1 c f ()) = gfields
          | Just v <- gnullary @f = dimap (const ()) (const v) oneP
          | otherwise = jsonKeyVal (Text.pack "contents") gcontents

gconName :: forall (c :: GHC.Meta). GHC.Constructor c => String
gconName = GHC.conName (undefined :: GHC.C1 c GHC.U1 ())

class GFields f where
  gfields :: JsonObj p => p (f x) (f x)
instance (GHC.Selector s, Json a) => GFields (GHC.S1 s (GHC.K1 i a)) where
  gfields = dimap (GHC.unK1 . GHC.unM1) (GHC.M1 . GHC.K1) $
    jsonKeyVal (Text.pack (GHC.selName (undefined :: GHC.S1 s (GHC.K1 i a) ()))) json
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

productIso :: Iso ((f GHC.:*: g) x) ((f GHC.:*: g) x) (f x, g x) (f x, g x)
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
