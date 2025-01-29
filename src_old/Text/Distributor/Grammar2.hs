module Text.Distributor.Grammar2
  ( Syntactic (..)
  , Grammatical (..)
  ) where

import Control.Lens
import Control.Lens.Internal.FunList
import Control.Lens.PartialIso
import Control.Lens.Stream
import Data.Function
import Data.Profunctor.Distributor
import Data.Profunctor.Monoidal

class
  ( PartialDistributor p
  , Tokenized c c p
  , Stream' s c
  , Eq c
  ) => Syntactic s c p where
    stream :: s -> p x ()
    stream str = case view _HeadTailMay str of
      Nothing -> pureP ()
      Just (h,t) -> (only h ?< anyToken) >* stream t

class Syntactic s c p => Grammatical s c p where
  rule :: String -> p x y -> p x y
  rule e p = ruleRec @s e (\_ -> p)
  ruleRec :: String -> (p x y -> p x y) -> p x y
  ruleRec _ = fix
