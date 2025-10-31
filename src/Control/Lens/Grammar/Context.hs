module Control.Lens.Grammar.Context
  ( Subtextual (..)
  , ReadIx (..)
  , Ctx (..)
  ) where

import Control.Applicative
import Control.Lens (uncons)
import Control.Lens.Grammar.Stream
import Control.Monad
import Control.Monad.Codensity
import GHC.Exts
import Text.ParserCombinators.ReadP (ReadP)
import qualified Text.ParserCombinators.ReadP as Text

class (IsStream s, MonadPlus m) => Subtextual s m where
  getItem :: m (Item s)
  lookStream :: m s

instance Subtextual String ReadP where
  getItem = Text.get
  lookStream = Text.look





-----------------------

newtype ReadIx s t a = ReadIx (Codensity (Ctx s t) a)

data Ctx s t a
  = Get (Item s -> Ctx s t a)
  | Look (s -> Ctx s t a)
  | Result a (Ctx s t a)
  | Final [(a,t)]
  deriving Functor
instance IsStream s => Applicative (Ctx s s) where
  pure x = Result x (Final empty)
  (<*>) = ap
instance IsStream s => MonadPlus (Ctx s s)
instance IsStream s => Monad (Ctx s s) where
  (Get f)         >>= k = Get (\c -> f c >>= k)
  (Look f)        >>= k = Look (\s -> f s >>= k)
  (Result x p)    >>= k = k x <|> (p >>= k)
  (Final rs)      >>= k = Final (rs >>= \(x,s) -> run (k x) s)
instance IsStream s => MonadFail (Ctx s s) where
  fail _ = Final []
instance IsStream s => Alternative (Ctx s s) where
  empty = Final []
  Get f1     <|> Get f2     = Get (\c -> f1 c <|> f2 c)
  Result x p <|> q          = Result x (p <|> q)
  p          <|> Result x q = Result x (p <|> q)
  -- TODO: uncons
  Final []     <|> p        = p
  p            <|> Final [] = p
  Final r      <|> Final t  = Final (r <|> t)
  Final (r:rs) <|> Look f   = Look (\s -> Final (pure r <|> (rs <|> run (f s) s)))
  Final (r:rs) <|> p        = Look (\s -> Final (pure r <|> (rs <|> run p s)))
  Look f       <|> Final r  = Look (\s -> Final (case run (f s) s of
                                []     -> r
                                (x:xs) -> (pure x <|> xs) <|> r))
  p            <|> Final r  = Look (\s -> Final (case run p s of
                                []     -> r
                                (x:xs) -> (pure x <|> xs) <|> r))
  Look f     <|> Look g     = Look (\s -> f s <|> g s)
  Look f     <|> p          = Look (\s -> f s <|> p)
  p          <|> Look f     = Look (\s -> p <|> f s)
run :: (IsStream s, Alternative f) => Ctx s s a -> s -> f (a, s)
run (Get f)         cs    = case uncons cs of
                              Nothing    -> empty
                              Just (c,s) -> run (f c) s
run (Look f)        s     = run (f s) s
run (Result x p)    s     = pure (x,s) <|> run p s
run (Final rs)      _     = foldr (<|>) empty (map pure rs)
