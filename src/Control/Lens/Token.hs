module Control.Lens.Token
  ( -- * Token
    Categorized (..)
  , Tokenized (..)
  , satisfy
  , tokens
  , Tokenizor
    -- * Like
  , oneLike
  , anyLike
  , optLike
  , reqLike
    -- * Unicode
  , GeneralCategory (..)
  ) where

import Control.Lens
import Control.Lens.PartialIso
import Data.Char
import Data.Profunctor
import Data.Profunctor.Distributor
import Data.Word

class (Eq a, Eq (Categorize a)) => Categorized a where
  type Categorize a
  type Categorize a = ()
  categorize :: a -> Categorize a
  default categorize :: Categorize a ~ () => a -> Categorize a
  categorize _ = ()
  decategorize :: Categorize a -> [a]
  decategorize _ = []
instance Categorized Char where
  type Categorize Char = GeneralCategory
  categorize = generalCategory
  decategorize = \case
    LowercaseLetter -> "Ll"
    UppercaseLetter -> "Lu"
    TitlecaseLetter -> "Lt"
    ModifierLetter -> "Lm"
    OtherLetter -> "Lo"
    NonSpacingMark -> "Mn"
    SpacingCombiningMark -> "Mc"
    EnclosingMark -> "Me"
    DecimalNumber -> "Nd"
    LetterNumber -> "Nl"
    OtherNumber -> "No"
    ConnectorPunctuation -> "Pc"
    DashPunctuation -> "Pd"
    OpenPunctuation -> "Ps"
    ClosePunctuation -> "Pe"
    InitialQuote -> "Pi"
    FinalQuote -> "Pf"
    OtherPunctuation -> "Po"
    MathSymbol -> "Sm"
    CurrencySymbol -> "Sc"
    ModifierSymbol -> "Sk"
    OtherSymbol -> "So"
    Space -> "Zs"
    LineSeparator -> "Zl"
    ParagraphSeparator -> "Zp"
    Control -> "Cc"
    Format -> "Cf"
    Surrogate -> "Cs"
    PrivateUse -> "Co"
    NotAssigned -> "Cn"
instance Categorized Word8
instance Categorized ()

class Categorized (Token p) => Tokenized p where
  type Token p

  anyToken :: p

  token :: Token p -> p
  default token
    :: (p ~ q (Token p) (Token p), Choice q, Cochoice q)
    => Token p -> p
  token = satisfy . token

  inClass :: [Token p] -> p
  default inClass
    :: (p ~ q (Token p) (Token p), Choice q, Cochoice q)
    => [Token p] -> p
  inClass = satisfy . inClass

  notInClass :: [Token p] -> p
  default notInClass
    :: (p ~ q (Token p) (Token p), Choice q, Cochoice q)
    => [Token p] -> p
  notInClass = satisfy . notInClass

  inCategory :: Categorize (Token p) -> p
  default inCategory
    :: (p ~ q (Token p) (Token p), Choice q, Cochoice q)
    => Categorize (Token p) -> p
  inCategory = satisfy . inCategory

  notInCategory :: Categorize (Token p) -> p
  default notInCategory
    :: (p ~ q (Token p) (Token p), Choice q, Cochoice q)
    => Categorize (Token p) -> p
  notInCategory = satisfy . notInCategory

instance Categorized c => Tokenized (c -> Bool) where
  type Token (c -> Bool) = c
  anyToken _ = True
  token = (==)
  inClass = flip elem
  notInClass = flip notElem
  inCategory = lmap categorize . (==)
  notInCategory = lmap categorize . (/=)

instance (Monoid a, Tokenized b) => Tokenized (a,b) where
  type Token (a,b) = Token b
  anyToken = pure anyToken
  token = pure . token
  inClass = pure . inClass
  notInClass = pure . notInClass
  inCategory = pure . inCategory
  notInCategory = pure . notInCategory

satisfy
  :: ( Choice q, Cochoice q
     , Tokenized p, p ~ q (Token p) (Token p)
     )
  => (Token p -> Bool) -> p
satisfy f = satisfied f >?< anyToken

type Tokenizor a p = (Tokenized (p a a), Token (p a a) ~ a)

tokens
  :: ( AsEmpty s
     , Cons s s a a
     , Monoidal p
     , Choice p
     , Tokenizor a p
     )
  => [a]
  -> p s s
tokens [] = asEmpty
tokens (a:as) = token a >:< tokens as

{- |
`oneLike` consumes one token
of a given token's category while parsing,
and produces the given token while printing.
-}
oneLike :: forall c p. (Profunctor p, Tokenizor c p) => c -> p () ()
oneLike c = dimap (\_ -> c) (\(_::c) -> ()) (inCategory (categorize c))

{- |
`anyLike` consumes tokens
of a given token's category while parsing,
and produces no tokens printing.
-}
anyLike :: forall c p. (Distributor p, Tokenizor c p) => c -> p () ()
anyLike c = dimap (\_ -> []::[c]) (\(_::[c]) -> ())
  (manyP (inCategory (categorize c)))

{- |
`optLike` consumes tokens
of a given token's category while parsing,
and produces the given token while printing.
-}
optLike :: forall c p. (Distributor p, Tokenizor c p) => c -> p () ()
optLike c = dimap (\_ -> [c]::[c]) (\(_::[c]) -> ())
  (manyP (inCategory (categorize c)))

{- |
`reqLike` accepts one or more tokens,
of a given token's category while parsing,
and produces the given token while printing.
-}
reqLike :: forall c p. (Distributor p, Tokenizor c p) => c -> p () ()
reqLike c = dimap (\_ -> (c,[]::[c])) (\(_::c, _::[c]) -> ())
  (inCategory (categorize c) >*< manyP (inCategory (categorize c)))
