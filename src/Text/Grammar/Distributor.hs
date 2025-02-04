module Text.Grammar.Distributor
  ( Syntax (tokens, rule, ruleRec)
  , token
  , satisfy
  , restOfStream
  , endOfStream
  , char
  , ReadSyntax (..), runReadSyntax, readSyntax
  , ShowSyntax (ShowSyntax), runShowSyntax, showSyntax
  , Production (..), production
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.PartialIso
import Control.Lens.Token
import Data.Char
import Data.Coerce
import Data.Function
import Data.Profunctor
import Data.Profunctor.Distributor
import Data.String
import Text.ParserCombinators.ReadP hiding (many, satisfy, char, sepBy)
import Witherable

class
  ( Alternator p
  , Filtrator p
  , Eq c
  , Tokenized c c p
  ) => Syntax c p where

    tokens
      :: [c] -- ^ terminal symbol
      -> p () ()
    tokens str = case uncons str of
      Nothing -> oneP
      Just (h,t) -> token h *> tokens t

    rule
      :: String -- ^ nonterminal symbol
      -> p a b -- ^ definition
      -> p a b
    rule e p = ruleRec e (const p)

    ruleRec
      :: String -- ^ nonterminal symbol
      -> (p a b -> p a b) -- ^ recursive definition
      -> p a b
    ruleRec _ = fix

token :: Syntax c p => c -> p () ()
token c = mapCoprism (only c) anyToken

satisfy :: Syntax c p => (c -> Bool) -> p c c
satisfy f = mapPartialIso (_Satisfy f) anyToken

restOfStream :: Syntax c p => p [c] [c]
restOfStream = manyP anyToken

endOfStream :: Syntax c p => p () ()
endOfStream = mapCoprism _Empty restOfStream

char :: Syntax Char p => GeneralCategory -> p Char Char
char cat = rule (show cat) $
  satisfy $ \ch -> cat == generalCategory ch

newtype ShowSyntax a b = ShowSyntax (a -> Maybe ShowS)
instance Profunctor ShowSyntax where
  dimap f _ (ShowSyntax sh) = ShowSyntax (sh . f)
instance Functor (ShowSyntax a) where fmap = rmap
instance Applicative (ShowSyntax a) where
  pure _ = ShowSyntax (const (Just id))
  ShowSyntax sh0 <*> ShowSyntax sh1 =
    ShowSyntax (liftA2 (liftA2 (.)) sh0 sh1)
instance Alternative (ShowSyntax a) where
  empty = ShowSyntax (const Nothing)
  ShowSyntax sh0 <|> ShowSyntax sh1 =
    ShowSyntax (liftA2 (<|>) sh0 sh1)
  many (ShowSyntax sh) = ShowSyntax sh
  some (ShowSyntax sh) = ShowSyntax sh
instance Choice ShowSyntax where
  left' (ShowSyntax sh) =
    ShowSyntax (either sh (const Nothing))
  right' (ShowSyntax sh) =
    ShowSyntax (either (const Nothing) sh)
instance Cochoice ShowSyntax where
  unleft (ShowSyntax sh) = ShowSyntax (sh . Left)
  unright (ShowSyntax sh) = ShowSyntax (sh . Right)
instance Distributor ShowSyntax where
  manyP (ShowSyntax sh) = ShowSyntax shmany where
    shmany str =
      foldl (liftA2 (.)) (pure id) (map sh str)
instance Alternator ShowSyntax where
  someP (ShowSyntax sh) = ShowSyntax shsome where
    shsome str = do
      _ <- uncons str
      foldl (liftA2 (.)) (pure id) (map sh str)
instance Filtrator ShowSyntax
instance Filterable (ShowSyntax a) where
  mapMaybe = dimapMaybe Just
instance Tokenized Char Char ShowSyntax where
  anyToken = ShowSyntax (Just . (:))
instance Syntax Char ShowSyntax
instance IsString (ShowSyntax () ()) where fromString = tokens

newtype ReadSyntax a b = ReadSyntax (ReadP b)
instance Profunctor ReadSyntax where
  dimap _ g (ReadSyntax rd) = ReadSyntax (g <$> rd)
instance Functor (ReadSyntax a) where fmap = rmap
instance Applicative (ReadSyntax a) where
  pure b = ReadSyntax (pure b)
  ReadSyntax rd0 <*> ReadSyntax rd1 =
    ReadSyntax (rd0 <*> rd1)
instance Alternative (ReadSyntax a) where
  empty = ReadSyntax empty
  ReadSyntax rd0 <|> ReadSyntax rd1 =
    ReadSyntax (rd0 <|> rd1)
  many (ReadSyntax rd) = ReadSyntax (many rd)
  some (ReadSyntax rd) = ReadSyntax (some rd)
instance Choice ReadSyntax where
  left' (ReadSyntax rd) =
    ReadSyntax (Left <$> rd)
  right' (ReadSyntax rd) =
    ReadSyntax (Right <$> rd)
instance Cochoice ReadSyntax where
  unleft (ReadSyntax rd) =
    ReadSyntax (rd >>= either pure (const empty))
  unright (ReadSyntax rd) =
    ReadSyntax (rd >>= either (const empty) pure)
instance Distributor ReadSyntax where
  manyP (ReadSyntax rd) = ReadSyntax (many rd)
instance Alternator ReadSyntax where
  someP (ReadSyntax rd) = ReadSyntax (some rd)
instance Filtrator ReadSyntax
instance Filterable (ReadSyntax a) where
  mapMaybe = dimapMaybe Just
instance Tokenized Char Char ReadSyntax where
  anyToken = ReadSyntax get
instance Syntax Char ReadSyntax
instance IsString (ReadSyntax () ()) where fromString = tokens

runReadSyntax :: ReadSyntax a b -> String -> [(b, String)]
runReadSyntax (ReadSyntax rd) str = readP_to_S rd str

runShowSyntax :: ShowSyntax a b -> a -> Maybe String
runShowSyntax (ShowSyntax sh) a = ($ "") <$> sh a

showSyntax :: Show a => ShowSyntax a a
showSyntax = ShowSyntax (Just . shows)

readSyntax :: Read a => ReadSyntax a a
readSyntax = ReadSyntax (readS_to_P reads)

data Production c
  = Zero
  | Terminal [c]
  | NonTerminal String
  | Plus (Production c) (Production c)
  | Times (Production c) (Production c)
  | Optional (Production c)
  | Many (Production c)
  | Some (Production c)

makePrisms ''Production

production
  :: Syntax Char p
  => p (Production Char) (Production Char)
production = ruleRec "production" $ \pro ->
  dichainl1 _Plus (sepBy (tokens " | ")) (seqUence pro)
  where
    seqUence pro
      = rule "sequence"
      $ dichainl1 _Times (sepBy (token ' ')) (expression pro)
    expression pro
      = rule "expression"
      $ nonterminal
      <|> terminal
      <|> mapPrism _Optional (tokens "(" >* pro *< tokens ")?")
      <|> mapPrism _Many (tokens "(" >* pro *< tokens ")*")
      <|> mapPrism _Some (tokens "(" >* pro *< tokens ")+")
      <|> tokens "(" >* pro *< tokens ")"
    terminal
      = rule "terminal"
      . mapPrism _Terminal
      $ token '\"' >* manyP unreserved *< token '\"'
    nonterminal
      = rule "nonterminal"
      . mapPrism _NonTerminal
      $ token '<' >* manyP unreserved *< token '>'
    unreserved
      = rule "unreserved"
      . satisfy
      $ \ch -> ch `notElem` reserved
    reserved :: String = "\"<>|=()"

instance Show (Production Char) where
  show prod = maybe (error "bad production") id
    (runShowSyntax production prod)

data Grammar c a b = Grammar (Production c) [(String, Production c)]
instance Functor (Grammar c a) where fmap = rmap
instance Applicative (Grammar c a) where
  pure _ = Grammar (Terminal []) []
  Grammar (Terminal []) rules0 <*> Grammar s1 rules1 =
    Grammar s1 (rules0 <> rules1)
  Grammar s0 rules0 <*> Grammar (Terminal []) rules1 =
    Grammar s0 (rules0 <> rules1)
  Grammar s0 rules0 <*> Grammar s1 rules1 =
    Grammar (Times s0 s1) (rules0 <> rules1)
instance Alternative (Grammar c a) where
  empty = Grammar Zero []
  Grammar Zero rules0 <|> Grammar s1 rules1 =
    Grammar s1 (rules0 <> rules1)
  Grammar s0 rules0 <|> Grammar Zero rules1 =
    Grammar s0 (rules0 <> rules1)
  Grammar s0 rules0 <|> Grammar s1 rules1 =
    Grammar (Plus s0 s1) (rules0 <> rules1)
  many (Grammar s rules) = Grammar (Many s) rules
  some (Grammar s rules) = Grammar (Many s) rules
instance Profunctor (Grammar c) where
  dimap _ _ = coerce
instance Distributor (Grammar c) where
  zeroP = Grammar Zero []
  Grammar Zero rules0 >+< Grammar s1 rules1 =
    Grammar s1 (rules0 <> rules1)
  Grammar s0 rules0 >+< Grammar Zero rules1 =
    Grammar s0 (rules0 <> rules1)
  Grammar s0 rules0 >+< Grammar s1 rules1 =
    Grammar (Plus s0 s1) (rules0 <> rules1)
  optionalP (Grammar s rules) = Grammar (Optional s) rules
  manyP (Grammar s rules) = Grammar (Many s) rules
