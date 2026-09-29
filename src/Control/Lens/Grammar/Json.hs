module Control.Lens.Grammar.Json
  ( JsonGrammatical (..)
  , JsonVal (..)
  , JsonArr (..)
  , JsonObj (..)
  ) where

import Control.Lens
import Control.Lens.Grammar.BackusNaur
import Control.Lens.PartialIso
import Data.Profunctor.Distributor
import Data.Aeson
import Data.Aeson.Types
import Data.Scientific
import Data.Text

class JsonGrammatical a where
  json :: JsonVal p => p a a

class
  ( forall x y. BackusNaurForm (p x y)
  , Alternator p
  ) => JsonVal p where
    object :: (forall q. JsonObj q => q a b) -> p a b
    array :: (forall q. JsonArr q => q a b) -> p a b
    string :: p Text Text
    number :: p Scientific Scientific
    boolean :: p Bool Bool
    null :: p () ()
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

-- instances
instance JsonGrammatical Value where json = value
instance JsonGrammatical Text where json = string
instance JsonGrammatical Scientific where json = number
instance JsonGrammatical Bool where json = boolean
