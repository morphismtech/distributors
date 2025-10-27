module Control.Lens.Grammar.Kleene
  ( KleeneStarAlgebra (..)
  , RegEx (..)
  ) where

import Control.Applicative
import Control.Lens.Grammar.Symbol
import Control.Lens.Grammar.Token
import Data.Foldable
import Data.Monoid
import Prelude hiding ((*), (+))

class Monoid t => KleeneStarAlgebra t where
  starK, plusK, optK :: t -> t
  starK t = optK (starK t)
  plusK t = t <> starK t
  optK t = mempty >|< t
  (>|<) :: t -> t -> t
  default (>|<) :: (t ~ f a, Alternative f) => t -> t -> t
  (>|<) = (<|>)
  empK :: t
  default empK :: (t ~ f a, Alternative f) => t
  empK = empty
instance (Alternative f, Monoid t) => KleeneStarAlgebra (Ap f t)

data RegEx token
  = Terminal [token]
  | Sequence (RegEx token) (RegEx token)
  | Fail
  | Alternate (RegEx token) (RegEx token)
  | KleeneOpt (RegEx token)
  | KleeneStar (RegEx token)
  | KleenePlus (RegEx token)
  | AnyToken
  | OneOf [token]
  | NotOneOf [token]
  | AsIn (Categorize token)
  | NotAsIn (Categorize token)
  | NonTerminal String
deriving stock instance Categorized token => Eq (RegEx token)
deriving stock instance
  (Categorized token, Ord token, Ord (Categorize token))
    => Ord (RegEx token)
deriving stock instance
  (Categorized token, Read token, Read (Categorize token))
    => Read (RegEx token)
deriving stock instance
  (Categorized token, Show token, Show (Categorize token))
    => Show (RegEx token)
instance TerminalSymbol (RegEx token) where
  type Alphabet (RegEx token) = token
  terminal = Terminal . toList
instance Categorized token => Tokenized (RegEx token) where
  type Token (RegEx token) = token
  anyToken = AnyToken
  noToken = empK
  token a = terminal [a]
  notToken a = notOneOf [a]
  oneOf = OneOf . toList
  notOneOf = NotOneOf . toList
  asIn = AsIn
  notAsIn = NotAsIn
instance Categorized token => Semigroup (RegEx token) where
  Terminal [] <> rex = rex
  rex <> Terminal [] = rex
  Fail <> _ = empK
  _ <> Fail = empK
  Terminal str0 <> Terminal str1 = Terminal (str0 <> str1)
  KleeneStar rex0 <> rex1
    | rex0 == rex1 = plusK rex0
  rex0 <> KleeneStar rex1
    | rex0 == rex1 = plusK rex1
  rex0 <> rex1 = Sequence rex0 rex1
instance Categorized token => Monoid (RegEx token) where
  mempty = Terminal []
instance Categorized token => KleeneStarAlgebra (RegEx token) where
  empK = Fail
  optK Fail = mempty
  optK (Terminal []) = mempty
  optK (KleenePlus rex) = starK rex
  optK rex = KleeneOpt rex
  starK Fail = mempty
  starK (Terminal []) = mempty
  starK rex = KleeneStar rex
  plusK Fail = empK
  plusK (Terminal []) = mempty
  plusK rex = KleenePlus rex
  KleenePlus rex >|< Terminal [] = starK rex
  Terminal [] >|< KleenePlus rex = starK rex
  rex >|< Terminal [] = optK rex
  Terminal [] >|< rex = optK rex
  rex >|< Fail = rex
  Fail >|< rex = rex
  rex0 >|< rex1 | rex0 == rex1 = rex0
  rex0 >|< rex1 = Alternate rex0 rex1
instance NonTerminalSymbol (RegEx token) where
  nonTerminal = NonTerminal
