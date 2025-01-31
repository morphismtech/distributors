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
  , Stream s s c c
  ) => Syntactic s c p | p -> s where

    stream :: s -> p () ()
    stream str = case uncons str of
      Nothing -> oneP
      Just (h,t) -> (only h ?< anyToken) >* stream t

    rule :: String -> p a b -> p a b
    rule e p = ruleRec e (const p)

    ruleRec :: String -> (p a b -> p a b) -> p a b
    ruleRec _ = fix

data ShowRead a b = ShowRead (a -> Maybe ShowS) (ReadP b)
instance Tokenized Char Char ShowRead where
  anyToken = ShowRead (Just . (:)) get
instance Profunctor ShowRead where
  dimap f g (ShowRead s r) = ShowRead (s . f) (g <$> r)
instance Functor (ShowRead a) where fmap = rmap
instance Applicative (ShowRead a) where
  pure b = ShowRead (const (Just id)) (pure b)
  ShowRead s0 r0 <*> ShowRead s1 r1 =
    ShowRead (liftA2 (liftA2 (.)) s0 s1) (r0 <*> r1)
instance Alternative (ShowRead a) where
  empty = ShowRead (const Nothing) empty
  ShowRead s0 r0 <|> ShowRead s1 r1 =
    ShowRead (liftA2 (<|>) s0 s1) (r0 <|> r1)
  many (ShowRead s r) = ShowRead s (many r)
  some (ShowRead s r) = ShowRead s (some r)
instance Choice ShowRead where
  left' (ShowRead s r) =
    ShowRead (either s (const Nothing)) (Left <$> r)
  right' (ShowRead s r) =
    ShowRead (either (const Nothing) s) (Right <$> r)
instance Cochoice ShowRead where
  unleft (ShowRead s r) =
    ShowRead (s . Left) (r >>= either pure (const empty))
  unright (ShowRead s r) =
    ShowRead (s . Right) (r >>= either (const empty) pure)
instance Distributor ShowRead where
  manyP (ShowRead s r) = ShowRead
    (foldl (liftA2 (.)) (pure id) . map s . convertStream)
    (fmap convertStream (many r))
    where
      convertStream str = maybe Empty
        (\(h,t) -> cons h (convertStream t))
        (uncons str)
instance Alternator ShowRead
instance Filtrator ShowRead
instance Filterable (ShowRead a) where
  mapMaybe = dimapMaybe Just
instance Syntactic String Char ShowRead

showRead :: (Show a, Read a) => ShowRead a a
showRead = ShowRead (Just . shows) (readS_to_P reads)

readP :: ShowRead a b -> String -> Maybe b
readP (ShowRead _ r) s = fst <$> listToMaybe (readP_to_S r s)

showP :: ShowRead a b -> a -> Maybe String
showP (ShowRead s _) a = ($ "") <$> s a
