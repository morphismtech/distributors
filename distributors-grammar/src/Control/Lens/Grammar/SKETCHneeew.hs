module Token
  ( Categorize (..)
  , Tokenized (..)
  , TokenAlgebra (..)
  , TokenClass (..)
  , TokenExam (..)
  ) where

class
  ( Ord token
  , Enum (Categorize token)
  , Bounded (Categorize token)
  ) => Categorized token where
  type Categorize token :: Type
  categorize :: token -> Categorize token

class Categorized token => Tokenized token p | p -> token where
  anyToken :: p
  token :: token -> p
  oneOf :: Foldable f => f token -> p
  notOneOf :: Foldable f => f token -> p
  asIn :: Categorize token -> p
  notAsIn :: Categorize token -> p

class Tokenized token p => TokenAlgebra token p where
  tokenClass :: TokenClass token -> p

newtype TokenClass token = TokenClass (TokenExam token (TokenClass token))

data TokenExam token alg
  = OneOf (Set token)
  | NotOneOf (Set token) (CategoryTest token)
  | Alternate [alg]

data CategoryTest token
  = AndAsIn (Categorize token)
  | AndNotAsIn (Set (Categorize token))

module RegEx
  ( RegEx (..)
  , fromRegEx
  , KleeneStarAlgebra (..)
  , NotFollowed (..)
  , Tried (..)
  ) where

data RegEx token
  = Sequence [RegEx token]
  | KleeneStar (RegEx token)
  | KleeneOpt (RegEx token)
  | KleenePlus (RegEx token)
  | KleeneQuant Int (Maybe Int) (RegEx token)
  | RegExam (TokenExam token (RegEx token))
  | NotFollowedBy (RegEx token)
  | Try (RegEx token)

fromRegEx
  :: (KleeneStarAlgebra k, TokenAlgebra token k, NotFollowed token k, Tried k)
  -> RegEx token -> k

class NotFollowed token p where
  notFollowedBy :: RegEx token -> p

class Tried p where
  try :: p -> p

module BackusNaur
  ( Ruled (..)
  , BackusNaurForm (..)
  , Bnf (..)
  ) where

class Ruled name p where
  rule :: name -> p -> p

class Ruled name p => BackusNaurForm name p where
  ruleRec :: name -> (p -> p) -> p

data Bnf name rule = Bnf
  { startBnf :: Either name rule
  , rulesBnf :: Set (name, Either name rule)
  } deriving stock (Eq, Ord, Show, Read)

module Prec
  ( Preceded (..)
  ) where

class TerminalSymbol token p => Preceded p where
  prec :: Int -> p -> p
  precStep :: p -> p
  precReset :: p -> p
  precWith :: (Int -> p) -> p
