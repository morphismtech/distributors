{-|
Module      : Control.Lens.Grammar.Json
Description : bidirectional JSON grammars
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable

Unlike the token-stream `Data.Profunctor.Grammar.Parsor` &
`Data.Profunctor.Grammar.Printor`, `JsonParsor` & `JsonPrintor` operate
on the tree-shaped `Value`: `object` & `array` switch between three
sub-languages (`JsonVal`, `JsonObj`, `JsonArr`) so that `property` is
only usable inside an `object` & `element` only inside an `array`.

`JsonObj`'s `property` looks a field up by name, so combining two
properties with `>*<` merges two independent lookups against the /same/
`Object` (like the common aeson idiom
@MyRecord \<$\> o .: \"x\" \<*\> o .: \"y\"@) -- no left-to-right threading
is needed, since object keys are unordered. `JsonArr`'s `element`
by contrast describes a single, /homogeneous/ array slot; built-in
repetition (`manyP` \/ `someP` \/ `optionalP`) is repurposed on
`JsonParsor` & `JsonPrintor` to mean "the whole `Value` is a `Value`
array of these", following
[JsonGrammar](https://hackage.haskell.org/package/JsonGrammar)'s
homogeneous @el@. Consequently, generic combinators built from `>*<`
that assume left-to-right stream threading (like `someP`'s own default,
or `Data.Profunctor.Separator`'s @chain1@/@several@) are not meaningful
applied to `JsonParsor`\/`JsonPrintor` arrays; use `manyP`, `someP` &
`optionalP` directly instead.
-}

module Control.Lens.Grammar.Json
  ( JsonGrammatical (..)
  , JsonVal (..)
  , JsonArr (..)
  , JsonObj (..)
  , jsonPrint
  , jsonParse
  ) where

import Control.Applicative
import Control.Lens.Grammar.BackusNaur
import Control.Monad
import Data.Profunctor
import Data.Profunctor.Distributor
import Data.Profunctor.Filtrator
import Data.Aeson
import Data.Aeson.Key (fromText)
import Data.Aeson.Types
import qualified Data.Aeson.KeyMap as KeyMap
import Data.Scientific
import Data.Text (Text)
import qualified Data.Vector as V
import Witherable

class JsonGrammatical a where
  json :: JsonVal p => p a a

jsonPrint :: JsonGrammatical a => a -> Maybe Value
jsonPrint = runJsonPrintor json

jsonParse :: JsonGrammatical a => Value -> Parser a
jsonParse = runJsonParsor json

class
  ( forall x y. BackusNaurForm (p x y)
  , Alternator p
  ) => JsonVal p where
    object :: (forall q. JsonObj q => q a b) -> p a b
    array :: (forall q. JsonArr q => q a b) -> p a b
    string :: p Text Text
    number :: p Scientific Scientific
    boolean :: p Bool Bool
    value :: p Value Value

class
  ( forall x y. BackusNaurForm (p x y)
  , Alternator p
  ) => JsonArr p where
    element :: (forall q. JsonVal q => q a b) -> p a b

class
  ( forall x y. BackusNaurForm (p x y)
  , Alternator p
  ) => JsonObj p where
    property :: Text -> (forall q. JsonVal q => q a b) -> p a b

newtype JsonParsor a b = JsonParsor
  { runJsonParsor :: Value -> Parser b }

newtype JsonPrintor a b = JsonPrintor
  { runJsonPrintor :: a -> Maybe Value }

instance JsonGrammatical Value where json = value
instance JsonGrammatical Text where json = string
instance JsonGrammatical Scientific where json = number
instance JsonGrammatical Bool where json = boolean

-- JsonParsor instances

instance Functor (JsonParsor a) where
  fmap f (JsonParsor p) = JsonParsor (fmap f . p)
instance Profunctor JsonParsor where
  dimap _ g (JsonParsor p) = JsonParsor (fmap g . p)
instance Applicative (JsonParsor a) where
  pure b = JsonParsor (\_ -> pure b)
  JsonParsor f <*> JsonParsor x = JsonParsor (\v -> f v <*> x v)
instance Alternative (JsonParsor a) where
  empty = JsonParsor (\_ -> empty)
  JsonParsor p <|> JsonParsor q = JsonParsor (\v -> p v <|> q v)
instance Filterable (JsonParsor a) where
  mapMaybe f (JsonParsor p) = JsonParsor $ \v ->
    p v >>= maybe (fail "mapMaybe: no match") pure . f
instance Cochoice JsonParsor where
  unleft (JsonParsor p) = JsonParsor $ \v ->
    p v >>= either pure (\_ -> fail "unleft: unexpected Right")
  unright (JsonParsor p) = JsonParsor $ \v ->
    p v >>= either (\_ -> fail "unright: unexpected Left") pure
instance Filtrator JsonParsor
instance Choice JsonParsor where
  left' = alternate . Left
  right' = alternate . Right
instance Distributor JsonParsor where
  -- | The whole `Value` is treated as a `Value` array of repeated elements.
  manyP (JsonParsor p) = JsonParsor $
    withArray "array" (traverse p . V.toList)
  optionalP (JsonParsor p) = JsonParsor $ \case
    Null -> pure Nothing
    v -> Just <$> p v
instance Alternator JsonParsor where
  alternate = \case
    Left (JsonParsor p) -> JsonParsor (fmap Left . p)
    Right (JsonParsor p) -> JsonParsor (fmap Right . p)
  -- | `someP`'s default assumes `>*<` threads a stream left-to-right,
  -- which is not how `JsonParsor`'s `Applicative` behaves (both sides of
  -- @>*<@ run against the /same/ `Value`), so it's overridden directly.
  someP (JsonParsor p) = JsonParsor $
    withArray "array" $ \arr -> case V.toList arr of
      [] -> fail "expected a non-empty array"
      xs -> traverse p xs
instance BackusNaurForm (JsonParsor a b)

-- JsonPrintor instances

instance Functor (JsonPrintor a) where
  fmap _ (JsonPrintor p) = JsonPrintor p
instance Profunctor JsonPrintor where
  dimap f _ (JsonPrintor p) = JsonPrintor (p . f)
instance Applicative (JsonPrintor a) where
  pure _ = JsonPrintor (\_ -> Just (Object KeyMap.empty))
  JsonPrintor f <*> JsonPrintor x = JsonPrintor $ \a -> do
    v1 <- f a
    v2 <- x a
    case (v1,v2) of
      (Object o1, Object o2) -> Just (Object (KeyMap.union o1 o2))
      _ -> Nothing

instance Alternative (JsonPrintor a) where
  empty = JsonPrintor (\_ -> Nothing)
  JsonPrintor p <|> JsonPrintor q = JsonPrintor $ \a -> p a <|> q a
instance Filterable (JsonPrintor a) where
  mapMaybe _ (JsonPrintor p) = JsonPrintor p
instance Cochoice JsonPrintor where
  unleft (JsonPrintor p) = JsonPrintor (p . Left)
  unright (JsonPrintor p) = JsonPrintor (p . Right)
instance Filtrator JsonPrintor where
  filtrate (JsonPrintor p) = (JsonPrintor (p . Left), JsonPrintor (p . Right))
instance Choice JsonPrintor where
  left' = alternate . Left
  right' = alternate . Right
instance Distributor JsonPrintor where
  zeroP = JsonPrintor (\v -> case v of {})
  JsonPrintor p >+< JsonPrintor q = JsonPrintor (either p q)
  -- | The whole printed `Value` is a `Value` array of repeated elements.
  manyP (JsonPrintor p) = JsonPrintor $ \as ->
    Array . V.fromList <$> traverse p as
  optionalP (JsonPrintor p) = JsonPrintor $ maybe (Just Null) p
instance Alternator JsonPrintor where
  alternate = \case
    Left (JsonPrintor p) -> JsonPrintor (either p (\_ -> Nothing))
    Right (JsonPrintor p) -> JsonPrintor (either (\_ -> Nothing) p)
  -- | Printing a list never needs to reject emptiness the way parsing
  -- does, so `someP` is just `manyP` here (see `JsonParsor`'s `someP` for
  -- why the default, which assumes stream-threaded `>*<`, doesn't apply).
  someP = manyP
instance BackusNaurForm (JsonPrintor a b)

-- JsonVal, JsonArr & JsonObj instances

instance JsonVal JsonParsor where
  object sub = JsonParsor $ \v -> withObject "object" (\_ -> runJsonParsor sub v) v
  array sub = JsonParsor $ \v -> withArray "array" (\_ -> runJsonParsor sub v) v
  string = JsonParsor (withText "string" pure)
  number = JsonParsor (withScientific "number" pure)
  boolean = JsonParsor (withBool "boolean" pure)
  value = JsonParsor pure
instance JsonArr JsonParsor where
  element = id
instance JsonObj JsonParsor where
  property key sub = JsonParsor $ \v -> withObject "object" (\o ->
    case KeyMap.lookup (fromText key) o of
      Nothing -> fail ("missing property " <> show key)
      Just v' -> runJsonParsor sub v') v

instance JsonVal JsonPrintor where
  object (JsonPrintor sub) = JsonPrintor $ sub >=> \case
    obj@(Object _) -> Just obj; _ -> Nothing
  array (JsonPrintor sub) = JsonPrintor $ sub >=> \case
    arr@(Array _) -> Just arr; _ -> Nothing
  string = JsonPrintor (Just . String)
  number = JsonPrintor (Just . Number)
  boolean = JsonPrintor (Just . Bool)
  value = JsonPrintor Just
instance JsonArr JsonPrintor where
  element = id
instance JsonObj JsonPrintor where
  property key sub = JsonPrintor $ \a ->
    Object . KeyMap.singleton (fromText key) <$> runJsonPrintor sub a
