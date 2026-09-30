module Control.Lens.Grammar.Json
  ( -- * Json
    Json (..)
  , JsonKey (..)
  , JsonVal (..)
  , JsonString (..)
  , JsonArr (..)
  , JsonObj (..)
  , jsonPrint
  , jsonParse
    -- * Generics
  , GJson (..)
    -- * TypeScript
  , TypeScript (..)
  , TsType (..)
  , typescript
  , typeScriptGrammar
  , tsTypeGrammar
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.Grammar
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State.Strict
import Data.Aeson
import Data.Aeson.Key qualified as Key
import Data.Aeson.KeyMap (KeyMap)
import Data.Aeson.KeyMap qualified as KeyMap
import Data.Aeson.Types
import Data.Bifunctor.Joker
import Data.Functor.Compose
import Data.Map (Map)
import Data.Maybe
import Data.Monoid (First (..))
import Data.Profunctor (Star (..))
import Data.Profunctor.Strong
import Data.Scientific
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import GHC.Generics qualified as GHC
import GHC.IsList qualified as GHC

class Json a where
  json :: JsonVal p => p a a
  default json :: (GHC.Generic a, GJson (GHC.Rep a), JsonVal p) => p a a
  json = iso GHC.from GHC.to >~ gjson

class GJson f where gjson :: JsonVal p => p (f a) (f a)

class JsonKey a where jsonKey :: JsonString p => p a a

class
  ( Alternator p
  , forall x y. BackusNaurForm (p x y)
  , JsonString p
  ) => JsonVal p where
  jsonObject :: (forall q. JsonObj p q => q a b) -> p a b
  jsonArray :: (forall q. JsonArr p q => q a b) -> p a b
  jsonNumber :: p Scientific Scientific
  jsonBool :: p Bool Bool
  jsonVal :: p Value Value

class Profunctor p => JsonString p where
  jsonString :: p Text Text
  -- | A literal string.
  jsonText :: Text -> p () ()

class Alternator q => JsonArr p q | q -> p where
  jsonElement :: p a b -> q a b

class Alternator q => JsonObj p q | q -> p where
  jsonProperty
    :: (forall k. JsonString k => k a b)
    -> p c d
    -> q (a, c) (b, d)

jsonPrint :: Json a => a -> Value
jsonPrint = fromMaybe Null . printV json

jsonParse :: Json a => Value -> Parser a
jsonParse = parseV json

printV :: Star (Compose Maybe (Const (First Value))) a b -> a -> Maybe Value
printV p = fmap (fromMaybe Null . getFirst . getConst) . getCompose . runStar p

parseV :: Joker (ReaderT Value Parser) a b -> Value -> Parser b
parseV = runReaderT . runJoker

-- instances
instance JsonKey Text where
  jsonKey = jsonString
instance JsonKey Key where
  jsonKey = iso Key.toText Key.fromText >~ jsonString
instance Json Value where json = jsonVal
instance Json Bool where json = jsonBool
instance Json Scientific where json = jsonNumber
instance Json Text where json = jsonString
instance Json Key where json = jsonKey
instance Json Array where
  json = jsonArray (homogeneously (jsonElement jsonVal))
instance Json a => Json [a] where
  json = jsonArray (manyP (jsonElement json))
listIso
  :: GHC.IsList list
  => Iso list list [GHC.Item list] [GHC.Item list]
listIso = iso GHC.toList GHC.fromList
instance Json Object where
  json = jsonObject
    (listIso >~ manyP (keyIso >~ jsonProperty jsonString jsonVal))
      where
        keyIso = iso (first' Key.toText) (first' Key.fromText)
instance (Ord k, JsonKey k, Json v)
  => Json (Map k v) where
    json = jsonObject (listIso >~ manyP (jsonProperty jsonKey json))
instance JsonString (Joker (ReaderT Value Parser)) where
  jsonString = Joker (ReaderT (withText "String" pure))
  jsonText t = Joker $ ReaderT $ withText "String" $ \s ->
    if s == t then pure () else fail ("expected " <> show t)
instance JsonVal (Joker (ReaderT Value Parser)) where
  jsonObject p = Joker $ ReaderT $ withObject "Object" $ \obj -> do
    (b, rest) <- runStateT (runJoker p) obj
    if KeyMap.null rest then pure b
    else fail ("unknown fields: " <> show (KeyMap.keys rest))
  jsonArray p = Joker $ ReaderT $ withArray "Array" $ \arr -> do
    (b, n) <- runStateT (runReaderT (runJoker p) arr) 0
    if n == length arr then pure b
    else fail
      ( "cannot unpack array of length " <> show (length arr)
      <> " into " <> show n <> " elements" )
  jsonNumber = Joker (ReaderT (withScientific "Number" pure))
  jsonBool = Joker (ReaderT (withBool "Bool" pure))
  jsonVal = Joker (ReaderT pure)
instance JsonArr
  (Joker (ReaderT Value Parser))
  (Joker (ReaderT Array (StateT Int Parser))) where
  jsonElement p = Joker $ ReaderT $ \arr -> StateT $ \idx ->
    case arr ^? ix idx of
      Nothing -> fail "expected another element" <?> Index idx
      Just val -> (, idx + 1) <$> parseV p val <?> Index idx
instance JsonObj
  (Joker (ReaderT Value Parser))
  (Joker (StateT (KeyMap Value) Parser)) where
  jsonProperty k v = Joker $ StateT $ \obj -> do
    (b, key, val) <- choice
      [ (, key, val) <$> parseV k (String (Key.toText key)) <?> Key key
      | (key, val) <- KeyMap.toList obj
      ] <|> fail "key not found"
    d <- parseV v val <?> Key key
    pure ((b, d), KeyMap.delete key obj)
printer :: (a -> Maybe Value) -> Star (Compose Maybe (Const (First Value))) a b
printer f = Star (Compose . fmap (Const . First . Just) . f)
instance JsonString (Star (Compose Maybe (Const (First Value)))) where
  jsonString = printer (Just . String)
  jsonText t = printer (\_ -> Just (String t))
instance JsonVal (Star (Compose Maybe (Const (First Value)))) where
  jsonObject p = printer (fmap (Object . getConst) . getCompose . runStar p)
  jsonArray p = printer
    (fmap (Array . GHC.fromList . getConst) . getCompose . runStar p)
  jsonNumber = printer (Just . Number)
  jsonBool = printer (Just . Bool)
  jsonVal = printer Just
instance JsonArr
  (Star (Compose Maybe (Const (First Value))))
  (Star (Compose Maybe (Const [Value]))) where
  jsonElement p = Star (Compose . fmap (Const . pure) . printV p)
instance JsonObj
  (Star (Compose Maybe (Const (First Value))))
  (Star (Compose Maybe (Const (KeyMap Value)))) where
  jsonProperty k v = Star $ \(a, c) -> Compose $ do
    String key <- printV k a
    val <- printV v c
    pure (Const (KeyMap.singleton (Key.fromText key) val))

{- | Generic `Json` grammars, following aeson's
generic encoding with default options.

* A single constructor encodes its contents: a record as an object,
  a single field as its value, several fields as an array,
  and no fields as an empty array.
* A sum of nullary constructors encodes as the constructor name.
* Any other sum encodes as a tagged object,
  with a @"tag"@ property of the constructor name,
  and either the record fields, or a @"contents"@ property,
  or nothing, for a nullary constructor.

A generic grammar is a `rule` named after its datatype.
-}
instance (GHC.Datatype d, GSum f) => GJson (GHC.D1 d f) where
  gjson = rule (GHC.datatypeName (undefined :: GHC.D1 d f ())) $ dimap GHC.unM1 GHC.M1 $
    if gconCount @f == 1 then gsingle
    else if gallNullary @f then gnullaryTag
    else jsonObject gtagged

class GSum f where
  gconCount :: Int
  gallNullary :: Bool
  gsingle :: JsonVal p => p (f x) (f x)
  gnullaryTag :: JsonVal p => p (f x) (f x)
  gtagged :: (JsonVal p, JsonObj p q) => q (f x) (f x)

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
      if GHC.conIsRecord (undefined :: GHC.C1 c f ()) then jsonObject gfields
      else gcontents
    gnullaryTag = case gnullary of
      Nothing -> empty
      Just v -> dimap (const ()) (const (GHC.M1 v)) (jsonText (gconName @c))
    gtagged = dimap GHC.unM1 GHC.M1 (tag >* contents)
      where
        tag = dimap (const ((), ())) (const ()) $
          jsonProperty (jsonText (Text.pack "tag")) (jsonText (gconName @c))
        contents
          | GHC.conIsRecord (undefined :: GHC.C1 c f ()) = gfields
          | Just v <- gnullary = dimap (const ()) (const v) oneP
          | otherwise = dimap ((),) snd $
              jsonProperty (jsonText (Text.pack "contents")) gcontents

gconName :: forall (c :: GHC.Meta). GHC.Constructor c => Text
gconName = Text.pack (GHC.conName (undefined :: GHC.C1 c GHC.U1 ()))

-- | Record fields, as the properties of an object.
class GFields f where
  gfields :: (JsonVal p, JsonObj p q) => q (f x) (f x)
instance (GHC.Selector s, Json a) => GFields (GHC.S1 s (GHC.K1 i a)) where
  gfields = dimap (\(GHC.M1 (GHC.K1 a)) -> ((), a)) (\(_, a) -> GHC.M1 (GHC.K1 a)) $
    jsonProperty (jsonText key) json
    where
      key = Text.pack (GHC.selName (undefined :: GHC.S1 s (GHC.K1 i a) ()))
instance (GFields f, GFields g) => GFields (f GHC.:*: g) where
  gfields = productIso >~ gfields >*< gfields
instance GFields GHC.U1 where
  gfields = dimap (const ()) (const GHC.U1) oneP

-- | Positional fields, as the elements of an array.
class GElements f where
  gelements :: (JsonVal p, JsonArr p q) => q (f x) (f x)
instance Json a => GElements (GHC.S1 s (GHC.K1 i a)) where
  gelements = dimap (GHC.unK1 . GHC.unM1) (GHC.M1 . GHC.K1) (jsonElement json)
instance (GElements f, GElements g) => GElements (f GHC.:*: g) where
  gelements = productIso >~ gelements >*< gelements
instance GElements GHC.U1 where
  gelements = dimap (const ()) (const GHC.U1) oneP

productIso :: Iso ((f GHC.:*: g) x) ((f GHC.:*: g) x) (f x, g x) (f x, g x)
productIso = iso (\(a GHC.:*: b) -> (a, b)) (uncurry (GHC.:*:))

-- | Positional fields, as a single value or an array.
class GContents f where
  gcontents :: JsonVal p => p (f x) (f x)
instance Json a => GContents (GHC.S1 s (GHC.K1 i a)) where
  gcontents = dimap (GHC.unK1 . GHC.unM1) (GHC.M1 . GHC.K1) json
instance (GElements f, GElements g) => GContents (f GHC.:*: g) where
  gcontents = jsonArray gelements
instance GContents GHC.U1 where
  gcontents = jsonArray gelements

class GNullary f where
  gnullary :: Maybe (f x)
instance GNullary GHC.U1 where
  gnullary = Just GHC.U1
instance GNullary (GHC.S1 s f) where
  gnullary = Nothing
instance GNullary (f GHC.:*: g) where
  gnullary = Nothing

{- | A minimal TypeScript type expression,
sufficient to describe the JSON values of a `Json` grammar.
A `TsUnion` should be normalized, with either no alternatives,
printed as @never@, or at least two alternatives.
-}
data TsType
  = TsNamed String
  | TsUnknown
  | TsNull
  | TsBoolean
  | TsNumber
  | TsString
  | TsArray TsType
  | TsTuple [TsType]
  | TsRecord TsType
  | TsUnion [TsType]
  deriving stock (Eq, Ord, Show, Read)

makeNestedPrisms ''TsType

{- | TypeScript declarations, a `Bnf` of `TsType`s,
consisting of a distinguished starting type and a set of named types.
-}
newtype TypeScript = TypeScript {runTypeScript :: Bnf TsType}
  deriving stock (Show, Read)
  deriving newtype
    ( Eq, Ord
    , Semigroup, Monoid, KleeneStarAlgebra
    , NonTerminalSymbol, BackusNaurForm
    )

{- | Generate `TypeScript` declarations from a `Json` grammar. -}
typescript :: forall a. Json a => TypeScript
typescript = runGrammor (json @a)

{- | A context-free `Grammar` for `TypeScript`,
printed as a TypeScript module.

>>> import Data.Map (Map)
>>> import Data.Text (Text)
>>> let ts = typescript @(Map Text [Bool])
>>> mapM_ (putStrLn . ($ "")) (printG typeScriptGrammar ts :: Maybe (String -> String))
export type Start = { [key: string]: boolean[] };
-}
typeScriptGrammar :: Grammar Char TypeScript
typeScriptGrammar = rule "typescript" $ bnfIso >~
  terminal "export type Start = " >* tsTypeGrammar *< terminal ";"
  >*< (listIso >~ several noSep
    ( terminal "\ntype " >* nameG *< terminal " = "
      >*< tsTypeGrammar *< terminal ";" ))
  where
    bnfIso = iso
      (\(TypeScript (Bnf start rules)) -> (start, rules))
      (\(start, rules) -> TypeScript (Bnf start rules))

{- | A context-free `Grammar` for `TsType`s. -}
tsTypeGrammar :: Grammar Char TsType
tsTypeGrammar = ruleRec "type" $ \ty -> rule "union" $
  _TsUnion >? unionG ty <|> postfixG ty
  where
    unionG ty = postfixG ty >:<
      (terminal " | " >* several1 (sepWith " | ") (postfixG ty))
    postfixG ty = rule "postfix" $
      arraysIso >~ atomG ty >*< manyP (terminal "[]")
    arraysIso = iso peel (\(t, n) -> foldr (const TsArray) t n)
      where
        peel (TsArray t) = second' (() :) (peel t)
        peel t = (t, [])
    atomG ty = rule "atom" $ choice
      [ _TsUnknown >? terminal "unknown"
      , _TsNull >? terminal "null"
      , _TsBoolean >? terminal "boolean"
      , _TsNumber >? terminal "number"
      , _TsString >? terminal "string"
      , _TsUnion . _Empty >? terminal "never"
      , _TsTuple >? several (sepWith ", " & beginWith "[" & endWith "]") ty
      , _TsRecord >? terminal "{ [key: string]: " >* ty *< terminal " }"
      , _TsUnion >? terminal "(" >* unionG ty *< terminal ")"
      , _TsNamed >? nameG
      ]

-- | Type names begin with an uppercase letter, `_` or `$`,
-- so they can't be confused with lowercase keywords.
nameG :: Grammar Char String
nameG = rule "name" $
  (asIn @Char UppercaseLetter <|> oneOf "_$") >:< manyP (choice
    [ asIn @Char UppercaseLetter, asIn @Char LowercaseLetter
    , asIn @Char DecimalNumber, oneOf "_$" ])

-- | Normalized union.
unionTs :: [TsType] -> TsType
unionTs ts = case Set.toList (foldMap alts ts) of
  [t] -> t
  us | TsUnknown `elem` us -> TsUnknown
  us -> TsUnion us
  where
    alts (TsUnion us) = Set.fromList us
    alts t = Set.singleton t

alternatives :: TsType -> [TsType]
alternatives (TsUnion us) = us
alternatives t = [t]

neverTs :: TsType
neverTs = TsUnion []

-- | `TsType` of a JSON value.
-- A product of values types the first printed value,
-- since `oneP` prints nothing and a `jsonPrint` of nothing is @null@.
instance Semigroup TsType where
  t0 <> t1
    | t0 == neverTs || t1 == neverTs = neverTs
    | t0 == TsNull = t1
    | otherwise = t0
instance Monoid TsType where
  mempty = TsNull
instance KleeneStarAlgebra TsType where
  t0 >|< t1 = unionTs [t0, t1]
  zeroK = neverTs
  starK = optK
  plusK = id
instance NonTerminalSymbol TsType where
  nonTerminal = TsNamed

-- | `TsType` of the elements of a JSON array,
-- an array or tuple type or a union of them.
newtype TsElements = TsElements TsType
  deriving newtype (Eq, Ord)
instance Semigroup TsElements where
  TsElements s0 <> TsElements s1 = TsElements $
    unionTs [cat t0 t1 | t0 <- alternatives s0, t1 <- alternatives s1]
    where
      cat (TsTuple ts0) (TsTuple ts1) = TsTuple (ts0 <> ts1)
      cat t0 t1 = TsArray (unionTs (tsElements t0 <> tsElements t1))
instance Monoid TsElements where
  mempty = TsElements (TsTuple [])
instance KleeneStarAlgebra TsElements where
  TsElements s0 >|< TsElements s1 = TsElements (s0 >|< s1)
  zeroK = TsElements zeroK
  starK (TsElements s) =
    TsElements (TsArray (unionTs (foldMap tsElements (alternatives s))))
  plusK x = x <> starK x

tsElements :: TsType -> [TsType]
tsElements (TsTuple ts) = ts
tsElements (TsArray t) = [t]
tsElements _ = []

-- | `TsType` of the properties of a JSON object,
-- a record type or a union of them.
newtype TsProperties = TsProperties TsType
  deriving newtype (Eq, Ord)
instance Semigroup TsProperties where
  TsProperties s0 <> TsProperties s1 = TsProperties $
    unionTs [TsRecord (unionTs [v0, v1]) | v0 <- values s0, v1 <- values s1]
instance Monoid TsProperties where
  mempty = TsProperties (TsRecord neverTs)
instance KleeneStarAlgebra TsProperties where
  TsProperties s0 >|< TsProperties s1 = TsProperties (s0 >|< s1)
  zeroK = TsProperties zeroK
  starK (TsProperties s) = TsProperties (TsRecord (unionTs (values s)))
  plusK x = x <> starK x

values :: TsType -> [TsType]
values s = [v | TsRecord v <- alternatives s]

tsGrammor :: TsType -> Grammor TypeScript a b
tsGrammor = Grammor . TypeScript . liftBnf0

instance JsonString (Grammor TypeScript) where
  jsonString = tsGrammor TsString
  jsonText _ = tsGrammor TsString
instance JsonVal (Grammor TypeScript) where
  jsonObject p = Grammor (TypeScript (liftBnf1 (\(TsProperties t) -> t) (runGrammor p)))
  jsonArray p = Grammor (TypeScript (liftBnf1 (\(TsElements t) -> t) (runGrammor p)))
  jsonNumber = tsGrammor TsNumber
  jsonBool = tsGrammor TsBoolean
  jsonVal = tsGrammor TsUnknown
instance JsonArr (Grammor TypeScript) (Grammor (Bnf TsElements)) where
  jsonElement p =
    Grammor (liftBnf1 (TsElements . TsTuple . pure) (runTypeScript (runGrammor p)))
instance JsonObj (Grammor TypeScript) (Grammor (Bnf TsProperties)) where
  jsonProperty k v = Grammor $ liftBnf2 (\_ t -> TsProperties (TsRecord t))
    (runTypeScript (runGrammor k)) (runTypeScript (runGrammor v))
