module Control.Lens.Grammar.Context
  ( Reador (..)
  , Showor (..)
  , Subtext (..)
  , Context (..)
  ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Codensity
import Control.Monad.Reader
import Control.Monad.State
-- import Control.Monad.Trans
-- import Control.Monad.Trans.Indexed
-- import Data.Profunctor

newtype Reador s t m a b = Reador (Codensity (Subtext s t m) a)

newtype Showor s t w a b = Showor (Codensity (Context s t w a) b)

data Subtext s t m a
  = Get (s -> Subtext s t m a)
  | Put (m (a,t))
  | Subtext a (Subtext s t m a)

data Context s t w a b
  = Ask (a -> Context s t w a b)
  | Local (w (b, s -> t))
  | Context b (Context s t w a b)

-- instances

-- ReadIx
deriving stock instance Functor m => Functor (Subtext s t m)
instance (MonadPlus m) => Applicative (Subtext s s m) where
  pure x = Subtext x (Put empty)
  (<*>) = ap
instance (MonadPlus m) => MonadPlus (Subtext s s m)
instance (MonadPlus m) => Monad (Subtext s s m) where
  (Get f) >>= k = Get (\s -> f s >>= k)
  (Subtext x p) >>= k = k x <|> (p >>= k)
  (Put r) >>= k = Put (r >>= \(x,s) -> run (k x) s)
instance (MonadPlus m) => Alternative (Subtext s s m) where
  empty = Put empty
  -- most common case: two gets are combined
  -- results are delivered as soon as possible
  Subtext x p <|> q          = Subtext x (p <|> q)
  p          <|> Subtext x q = Subtext x (p <|> q)
  -- two finals are combined
  -- final + look becomes one look and one final (=optimization)
  -- final + sthg else becomes one look and one final
  Put r    <|> Put t    = Put (r <|> t)
  Put r    <|> Get f     = Get (\s -> Put (r <|> run (f s) s))
  Get f     <|> Put r    = Get (\s -> Put (run (f s) s <|> r))
  -- two looks are combined (=optimization)
  -- look + sthg else floats upwards
  Get f     <|> Get g     = Get (\s -> f s <|> g s)
run :: (Alternative f) => Subtext s s f a -> s -> f (a, s)
run (Get f)        s     = run (f s) s
run (Subtext x p)    s     = pure (x,s) <|> run p s
run (Put rs)      _     = rs
instance (MonadPlus m) => MonadReader s (Subtext s s m) where
  ask = get
  local f subtext = do
    s <- get
    modify f
    a <- subtext
    put s
    return a
instance (MonadPlus m) => MonadState s (Subtext s s m) where
  get = Get pure
  put s = Put (pure (pure s))
