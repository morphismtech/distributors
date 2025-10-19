module Data.Profunctor.Parsor
  ( -- *
--     Parsor
--   , Printor
--   , PP
--   , toParsor
--   , toPrintor
--   , pp
--   , Separator (..)
--   , SepBy (..)
--   , Stream1 (..)
--   , Stream (..)
--   , Tokenized (..)
--   , satisfy
--   , Categorized (..)
  ) where


-- newtype Parsor s t f a b = Parsor {runParsor :: s -> f (b,t)}
-- newtype Printor s t f a b = Printor {runPrintor :: a -> f (s -> t)}
-- newtype PP s t f a b = PP {runPP :: a -> s -> f (b, s -> t)}

-- toParsor :: Functor f => PP a b f s t -> Parsor s t f a b -- s -> a -> f (t, s -> b)
-- toPrintor :: Functor f => PP s t f a b -> Printor s t f a b
-- pp :: Applicative f => Parsor s t f a b -> Printor s t f a b -> PP s t f a b
