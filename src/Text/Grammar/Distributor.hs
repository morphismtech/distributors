module Text.Grammar.Distributor
  ( Syntactic (tokens, rule, ruleRec)
  , token
  , satisfy
  , restOfStream
  , endOfStream
  , char
  , ShowRead (ShowRead), showRead, readP, showP
  , Production (..), production
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.PartialIso
import Control.Lens.Token
import Data.Char
import Data.Function
import Data.Maybe
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

data ShowRead a b = ShowRead (a -> Maybe ShowS) (ReadP b)
instance Profunctor ShowRead where
  dimap f g (ShowRead sh rd) = ShowRead (sh . f) (g <$> rd)
instance Functor (ShowRead a) where fmap = rmap
instance Applicative (ShowRead a) where
  pure b = ShowRead (const (Just id)) (pure b)
  ShowRead sh0 rd0 <*> ShowRead sh1 rd1 =
    ShowRead (liftA2 (liftA2 (.)) sh0 sh1) (rd0 <*> rd1)
instance Alternative (ShowRead a) where
  empty = ShowRead (const Nothing) empty
  ShowRead sh0 rd0 <|> ShowRead sh1 rd1 =
    ShowRead (liftA2 (<|>) sh0 sh1) (rd0 <|> rd1)
  many (ShowRead sh rd) = ShowRead sh (many rd)
  some (ShowRead sh rd) = ShowRead sh (some rd)
instance Choice ShowRead where
  left' (ShowRead sh rd) =
    ShowRead (either sh (const Nothing)) (Left <$> rd)
  right' (ShowRead sh rd) =
    ShowRead (either (const Nothing) sh) (Right <$> rd)
instance Cochoice ShowRead where
  unleft (ShowRead sh rd) =
    ShowRead (sh . Left) (rd >>= either pure (const empty))
  unright (ShowRead sh rd) =
    ShowRead (sh . Right) (rd >>= either (const empty) pure)
instance Distributor ShowRead where
  manyP (ShowRead sh rd) = ShowRead shmany (many rd) where
    shmany str =
      foldl (liftA2 (.)) (pure id) (map sh str)
instance Alternator ShowRead where
  someP (ShowRead sh rd) = ShowRead shsome (some rd) where
    shsome str = do
      _ <- uncons str
      foldl (liftA2 (.)) (pure id) (map sh str)
instance Filtrator ShowRead
instance Filterable (ShowRead a) where
  mapMaybe = dimapMaybe Just
instance Tokenized Char Char ShowRead where
  anyToken = ShowRead (Just . (:)) get
instance Syntactic Char ShowRead
instance IsString (ShowRead () ()) where fromString = tokens

showRead :: (Show a, Read a) => ShowRead a a
showRead = ShowRead (Just . shows) (readS_to_P reads)

readP :: ShowRead a b -> String -> Maybe b
readP (ShowRead _ r) s = fst <$> listToMaybe (readP_to_S r s)

showP :: ShowRead a b -> a -> Maybe String
showP (ShowRead s _) a = ($ "") <$> s a

data Production c
  = Terminal [c]
  | NonTerminal String
  | Choice (Production c) (Production c)
  | Sequence (Production c) (Production c)
  | Optional (Production c)
  | Many (Production c)
  | Some (Production c)

makePrisms ''Production

production
  :: Syntactic Char p
  => p (Production Char) (Production Char)
production
  = ruleRec "production"
  $ \prod -> seqUence <|>
      mapPrism _Choice (seqUence *< tokens " | " >*< prod)
  where
    seqUence
      = ruleRec "sequence"
      $ \sequ -> term <|>
          mapPrism _Sequence (term *< token ' ' >*< sequ)
    term
      = rule "term"
      $ terminal <|> nonterminal
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
    reserved :: String = "\"<>|="
