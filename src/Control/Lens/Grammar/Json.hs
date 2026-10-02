{-# LANGUAGE RequiredTypeArguments #-}

module Control.Lens.Grammar.Json
  ( -- * Json
    Json (..)
  , JsonVal (..)
  , JsonKey (..)
  , JsonString (..)
  , JsonTup (..)
  , JsonObj (..)
    -- * TypeScript
  , TsType (..)
  , jsonType
    -- * Generics
  , GJson (..)
  ) where

import Control.Lens
import Control.Lens.Grammar
import Data.Map (Map)
import Data.Maybe
import Data.Scientific
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Vector (Vector)
import GHC.Generics qualified as GHC

class Json a where
  json :: JsonVal p => p a a
  default json :: (GHC.Generic a, GJson (GHC.Rep a), JsonVal p) => p a a
  json = iso GHC.from GHC.to >~ gjson

class
  ( Choice p
  , JsonString p
  , forall x y. BackusNaurForm (p x y)
  ) => JsonVal p where
  jsonNull :: p () ()
  jsonBool :: p Bool Bool
  jsonNumber :: p Scientific Scientific
  jsonArray :: p a b -> p (Vector a) (Vector b)
  jsonDict :: (forall q. JsonString q => q a b) -> p c d -> p (Map a c) (Map b d)
  jsonTuple :: (forall q. JsonTup q => q a b) -> p a b
  jsonObject :: (forall q. JsonObj q => q a b) -> p a b
  -- We don't want a `Monoidal` constraint because JSON isn't concatenable!
  -- Therefor, we don't want an `Alternator` constraint.
  -- Thus, we need `jsonAlt` and `jsonOr` instead.
  jsonAlt :: p a b -> p a b -> p a b
  jsonOr :: p a b -> p c d -> p (Either a c) (Either b d)

class JsonKey a where
  jsonKey :: JsonString p => p a a

class Profunctor p => JsonString p where
  jsonString :: p Text Text
  jsonText :: Text -> p () ()

class Monoidal p => JsonTup p where
  jsonVal :: (forall q. JsonVal q => q a b) -> p a b

class Monoidal p => JsonObj p where
  jsonKeyVal :: Text -> (forall q. JsonVal q => q a b) -> p a b

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

jsonType :: forall a. Json a => Bnf TsType TsType
jsonType = runGrammor (json @a)

class GJson f where gjson :: JsonVal p => p (f a) (f a)

-- instances
instance NonTerminalSymbol TsType where nonTerminal = TsNonTerminal
instance JsonKey Text where jsonKey = jsonString
instance Json Text where json = jsonString
instance Json Bool where json = jsonBool
instance Json Scientific where json = jsonNumber
instance Json a => Json (Vector a) where json = jsonArray json
instance (JsonKey a, Json b) => Json (Map a b) where json = jsonDict jsonKey json
instance Json a => Json (Maybe a) where json = eotMaybe >~ json `jsonOr` jsonNull
instance JsonString (Grammor (Bnf TsType TsType)) where
  jsonString = Grammor (pure TsString)
  jsonText _ = Grammor (pure TsString)
instance JsonVal (Grammor (Bnf TsType TsType)) where
  jsonNull = Grammor (pure TsNull)
  jsonBool = Grammor (pure TsBoolean)
  jsonNumber = Grammor (pure TsNumber)
  jsonArray (Grammor b) = Grammor (TsArray <$> b)
  jsonDict _ (Grammor v) = Grammor (TsDict <$> v)
  jsonTuple tup =
    let Bnf types rules = runGrammor tup
    in Grammor (Bnf (TsTuple types) rules)
  jsonObject obj =
    let Bnf fields rules = runGrammor obj
    in Grammor (Bnf (TsObject fields) rules)
  jsonAlt (Grammor b0) (Grammor b1) = Grammor (liftA2 tsOr b0 b1)
  jsonOr (Grammor b0) (Grammor b1) = Grammor (liftA2 tsOr b0 b1)
tsOr :: TsType -> TsType -> TsType
tsOr t0 t1
  | t0 == t1 = t0
  | t0 == TsNever = t1
  | t1 == TsNever = t0
  | otherwise = TsUnion t0 t1
instance JsonTup (Grammor (Bnf TsType [TsType])) where
  jsonVal g =
    let Bnf start rules = runGrammor g
    in Grammor (Bnf [start] rules)
instance JsonObj (Grammor (Bnf TsType [(Text, TsType)])) where
  jsonKeyVal k v =
    let
      Bnf start rules = runGrammor v
    in
      Grammor (Bnf [(k,start)] rules)

instance (GHC.Datatype d, GSum f) => GJson (GHC.D1 d f) where
  gjson = rule (GHC.datatypeName (undefined :: GHC.D1 d f ())) $ dimap GHC.unM1 GHC.M1 $
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
  gsingle = sumIso >~ gsingle `jsonOr` gsingle
  gnullaryTag = sumIso >~ gnullaryTag `jsonOr` gnullaryTag
  gtagged = sumIso >~ gtagged `jsonOr` gtagged

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
      Just v -> dimap (const ()) (const (GHC.M1 v)) (jsonText (gconName @c))
    gtagged = dimap GHC.unM1 GHC.M1 (jsonObject (tag >* contents))
      where
        tag :: JsonObj q => q () ()
        tag = jsonKeyVal (Text.pack "tag") (jsonText (gconName @c))
        contents :: JsonObj q => q (f x) (f x)
        contents
          | GHC.conIsRecord (undefined :: GHC.C1 c f ()) = gfields
          | Just v <- gnullary @f = dimap (const ()) (const v) oneP
          | otherwise = jsonKeyVal (Text.pack "contents") gcontents

gconName :: forall (c :: GHC.Meta). GHC.Constructor c => Text
gconName = Text.pack (GHC.conName (undefined :: GHC.C1 c GHC.U1 ()))

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
