module Control.Lens.Grammar.Context
  ( ReadIx (..)
  , Subtext (..)
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.Grammar.Stream
import Control.Monad
import Control.Monad.Codensity
import Control.Monad.Reader
-- import Control.Monad.Trans
-- import Control.Monad.Trans.Indexed
import Data.Profunctor
import GHC.Exts

newtype ReadIx s t m a = ReadIx (Codensity (Subtext s t m) a)

data Subtext s t m a
  = Get (Item s -> Subtext s t m a)
  | Look (s -> Subtext s t m a)
  | Result a (Subtext s t m a)
  | Final (m (a,t))

-- instances
deriving stock instance Functor m => Functor (Subtext s t m)
instance (IsStream s, MonadPlus m) => Applicative (Subtext s s m) where
  pure x = Result x (Final empty)
  (<*>) = ap
instance (IsStream s, MonadPlus m) => MonadPlus (Subtext s s m)
instance (IsStream s, MonadPlus m) => Monad (Subtext s s m) where
  (Get f)     >>= k = Get (\c -> f c >>= k)
  (Look f)   >>= k = Look (\s -> f s >>= k)
  (Result x p)    >>= k = k x <|> (p >>= k)
  (Final rs)      >>= k = Final (rs >>= \(x,s) -> run (k x) s)
instance (IsStream s, MonadPlus m) => Alternative (Subtext s s m) where
  empty = Final empty
  -- most common case: two gets are combined
  Get f1     <|> Get f2     = Get (\c -> f1 c <|> f2 c)
  -- results are delivered as soon as possible
  Result x p <|> q          = Result x (p <|> q)
  p          <|> Result x q = Result x (p <|> q)
  -- two finals are combined
  -- final + look becomes one look and one final (=optimization)
  -- final + sthg else becomes one look and one final
  Final r    <|> Final t    = Final (r <|> t)
  Final r    <|> Look f     = Look (\s -> Final (r <|> run (f s) s))
  Final r    <|> p          = Look (\s -> Final (r <|> run p s))
  Look f     <|> Final r    = Look (\s -> Final (run (f s) s <|> r))
  p          <|> Final r    = Look (\s -> Final (run p s <|> r))
  -- two looks are combined (=optimization)
  -- look + sthg else floats upwards
  Look f     <|> Look g     = Look (\s -> f s <|> g s)
  Look f     <|> p          = Look (\s -> f s <|> p)
  p          <|> Look f     = Look (\s -> p <|> f s)
run :: (IsStream s, Alternative f) => Subtext s s f a -> s -> f (a, s)
run (Get f)         cs    = maybe empty (\(c,s) -> run (f c) s) (uncons cs)
run (Look f)        s     = run (f s) s
run (Result x p)    s     = pure (x,s) <|> run p s
run (Final rs)      _     = rs
instance (IsStream s, MonadPlus m) => MonadReader s (Subtext s s m) where
  ask = Look return
  local g = \case
    Get f -> Get (local g . f)
    Look f -> Look (f . g)
    Result x p -> Result x (local g p)
    Final r -> Final (fmap (second' g) r)
  reader f = Look (return . f)
