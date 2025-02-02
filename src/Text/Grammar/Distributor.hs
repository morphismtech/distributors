module Text.Grammar.Distributor
  ( Syntactic (tokens, rule, ruleRec)
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
import Control.Lens.Bifocal
import Control.Lens.PartialIso
import Control.Lens.Token
import Data.Char
import Data.Function
import Data.Profunctor
import Data.Profunctor.Distributor
import Data.String
import Text.ParserCombinators.ReadP hiding (many, satisfy, char)
import Witherable

class
  ( Alternator p
  , Filtrator p
  , Eq c
  , Tokenized c c p
  ) => Syntactic c p where

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

token :: Syntactic c p => c -> p () ()
token c = mapCoprism (only c) anyToken

satisfy :: Syntactic c p => (c -> Bool) -> p c c
satisfy f = mapPartialIso (_Satisfy f) anyToken

restOfStream :: Syntactic c p => p [c] [c]
restOfStream = manyP anyToken

endOfStream :: Syntactic c p => p () ()
endOfStream = mapCoprism _Empty restOfStream

char :: Syntactic Char p => GeneralCategory -> p Char Char
char cat = rule (show cat) $
  satisfy $ \ch -> cat == generalCategory ch

data ShowSyntax a b = ShowSyntax (a -> Maybe ShowS)
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
instance Syntactic Char ShowSyntax
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
instance Syntactic Char ReadSyntax
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
  = Terminal [c]
  | NonTerminal String
  | Choice (Production c) (Production c)
  | Sequence (Production c) (Production c)
  | Optional (Production c)
  | Many (Production c)
  | Some (Production c)
  deriving (Show, Read)

makePrisms ''Production

production
  :: Syntactic Char p
  => p (Production Char) (Production Char)
production
  = produ
  where
    produ
      = ruleRec "production"
      $ \prod -> seqUence <|>
          mapBifocal _Choice (seqUence *< tokens " | " >*< prod)
    seqUence
      = ruleRec "sequence"
      $ \sequ -> term <|>
          mapBifocal _Sequence (term *< token ' ' >*< sequ)
    term
      = rule "term"
      $ terminal <|> nonterminal
    terminal
      = rule "terminal"
      . mapBifocal _Terminal
      $ token '\"' >* manyP unreserved *< token '\"'
    nonterminal
      = rule "nonterminal"
      . mapBifocal _NonTerminal
      $ token '<' >* manyP unreserved *< token '>'
    unreserved
      = rule "unreserved"
      . satisfy
      $ \ch -> ch `notElem` reserved
    reserved :: String = "\"<>|="
