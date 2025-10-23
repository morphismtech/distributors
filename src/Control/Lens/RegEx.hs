module Control.Lens.RegEx
  ( -- *
    RegEx (..)
  , TerminalSymbol (..)
  , KleeneStarAlgebra (..)
  , normRegEx
  , Terminator
  ) where

import Control.Lens
import Control.Lens.PartialIso
import Control.Lens.Token
import Data.Profunctor
import Data.Profunctor.Distributor

data RegEx c
  = Terminal [c]
  | Sequence (RegEx c) (RegEx c)
  | Fail
  | Alternate (RegEx c) (RegEx c)
  | KleeneOpt (RegEx c)
  | KleeneStar (RegEx c)
  | KleenePlus (RegEx c)
  | AnyToken
  | InClass [c]
  | NotInClass [c]
  | InCategory (Categorize c)
  | NotInCategory (Categorize c)
  | NonTerminal String

class TerminalSymbol s where
  type Alphabet s
  terminal :: [Alphabet s] -> s
  default terminal :: (s ~ p () (), Monoidal p, Cochoice p, Tokenizor c p, c ~ Alphabet s) => [Alphabet s] -> s
  terminal [] = oneP
  terminal (a:as) = only a ?< anyToken *> terminal as

class Monoid a => KleeneStarAlgebra a where
  starK :: a -> a
  plusK :: a -> a
  optK :: a -> a
  altK :: a -> a -> a
  failK :: a

normRegEx :: Categorized c => RegEx c -> RegEx c
normRegEx = \case
  Sequence rex1 rex2 -> normRegEx rex1 <> normRegEx rex2
  Alternate rex1 rex2 -> normRegEx rex1 `altK` normRegEx rex2
  KleeneOpt rex -> optK (normRegEx rex)
  KleeneStar rex -> starK (normRegEx rex)
  KleenePlus rex -> plusK (normRegEx rex)
  rex -> rex

type Terminator c p =
  ( TerminalSymbol (p () ())
  , Alphabet (p () ()) ~ c
  )

deriving stock instance Categorized c => Eq (RegEx c)
deriving stock instance
  (Categorized c, Ord c, Ord (Categorize c)) => Ord (RegEx c)
deriving stock instance
  (Categorized c, Read c, Read (Categorize c)) => Read (RegEx c)
deriving stock instance
  (Categorized c, Show c, Show (Categorize c)) => Show (RegEx c)
instance TerminalSymbol (RegEx c) where
  type Alphabet (RegEx c) = c
  terminal = Terminal
instance Monoid a => TerminalSymbol (a, RegEx c) where
  type Alphabet (a, RegEx c) = c
  terminal = pure . terminal
instance Categorized c => Tokenized (RegEx c) where
  type Token (RegEx c) = c
  anyToken = AnyToken
  token c = Terminal [c]
  inClass = InClass
  notInClass = NotInClass
  inCategory = InCategory
  notInCategory = NotInCategory
instance Categorized c => Semigroup (RegEx c) where
  Terminal [] <> rex = rex
  rex <> Terminal [] = rex
  Fail <> _ = failK
  _ <> Fail = failK
  Terminal str0 <> Terminal str1 = Terminal (str0 <> str1)
  KleeneStar rex0 <> rex1
    | rex0 == rex1 = plusK rex0
  rex0 <> KleeneStar rex1
    | rex0 == rex1 = plusK rex1
  rex0 <> rex1 = Sequence rex0 rex1
instance Categorized c => Monoid (RegEx c) where
  mempty = Terminal []
instance Categorized c => KleeneStarAlgebra (RegEx c) where
  failK = Fail
  optK Fail = mempty
  optK (Terminal []) = mempty
  optK (KleenePlus rex) = starK rex
  optK rex = KleeneOpt rex
  starK Fail = mempty
  starK (Terminal []) = mempty
  starK rex = KleeneStar rex
  plusK Fail = failK
  plusK (Terminal []) = mempty
  plusK rex = KleenePlus rex
  KleenePlus rex `altK` Terminal [] = starK rex
  Terminal [] `altK` KleenePlus rex = starK rex
  rex `altK` Terminal [] = optK rex
  Terminal [] `altK` rex = optK rex
  rex `altK` Fail = rex
  Fail `altK` rex = rex
  rex0 `altK` rex1 | rex0 == rex1 = rex0
  rex0 `altK` rex1 = Alternate rex0 rex1
instance (Monoid a, KleeneStarAlgebra b)
  => KleeneStarAlgebra (a,b) where
    starK = fmap starK
    plusK = fmap plusK
    optK = fmap optK
    failK = pure failK
    altK = liftA2 altK
