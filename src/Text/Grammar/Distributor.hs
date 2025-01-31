module Text.Grammar.Distributor
  ( Syntactic (stream, rule, ruleRec)
  , ShowRead (ShowRead), showRead, readP, showP
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.PartialIso
import Control.Lens.Token
import Data.Function
import Data.Maybe
import Data.Profunctor
import Data.Profunctor.Distributor
import Text.ParserCombinators.ReadP hiding (many)
import Witherable

class
  ( Alternator p
  , Filtrator p
  , Eq c
  , Tokenized c c p
  ) => Syntactic c p where

    stream :: [c] -> p () ()
    stream str = case uncons str of
      Nothing -> oneP
      Just (h,t) -> mapCoprism (only h) anyToken >* stream t

    rule :: String -> p a b -> p a b
    rule e p = ruleRec e (const p)

    ruleRec :: String -> (p a b -> p a b) -> p a b
    ruleRec _ = fix

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
  manyP (ShowRead sh rd) = ShowRead shmany rdmany
    where
      shmany
        = foldl (liftA2 (.)) (pure id)
        . map sh
      rdmany = many rd
instance Alternator ShowRead where
  someP (ShowRead sh rd) = ShowRead shsome rdsome
    where
      shsome str = do
        (h, str') <- uncons str
        let str'' = h:str'
        foldl (liftA2 (.)) (pure id) (map sh str'')
      rdsome = some rd
instance Filtrator ShowRead
instance Filterable (ShowRead a) where
  mapMaybe = dimapMaybe Just
instance Tokenized Char Char ShowRead where
  anyToken = ShowRead (Just . (:)) get
instance Syntactic Char ShowRead

showRead :: (Show a, Read a) => ShowRead a a
showRead = ShowRead (Just . shows) (readS_to_P reads)

readP :: ShowRead a b -> String -> Maybe b
readP (ShowRead _ r) s = fst <$> listToMaybe (readP_to_S r s)

showP :: ShowRead a b -> a -> Maybe String
showP (ShowRead s _) a = ($ "") <$> s a
