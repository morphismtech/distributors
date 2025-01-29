module Control.Lens.Tint
  ( Tint
  , ATint
  , withTint
  , mapTint
  -- , cloneTint
  , Tinting (..)
  , runTinting
  ) where

import Control.Applicative
import Control.Lens.Internal.Token
import Data.Functor.Apply
import Data.Functor.Alt
import Data.Profunctor
import Data.Profunctor.Distributor
import Witherable

type Tint s t a b = forall p f.
  (Alternator p, Filtrator p, Alternative f, Filterable f)
    => p a (f b) -> p s (f t)

newtype Tinting a b s t = Tinting
  { unTinting
      :: forall f. (Alternative f, Filterable f)
      => ((s -> Maybe a) -> f b) -> f t
  }
instance Functor (Tinting a b s) where fmap = rmap
instance Apply (Tinting a b s) where
  Tinting x <.> Tinting y = Tinting (\sab -> liftA2 ($) (x sab) (y sab))
instance Applicative (Tinting a b s) where
  pure t = Tinting (\_ -> pure t)
  (<*>) = (<.>)
instance Alt (Tinting a b s) where
  Tinting x <!> Tinting y = Tinting (\sab -> x sab <|> y sab)
instance Alternative (Tinting a b s) where
  empty = Tinting (\_ -> empty)
  (<|>) = (<!>)
instance Filterable (Tinting a b s) where
  mapMaybe = dimapMaybe Just
instance Profunctor (Tinting a b) where
  dimap f g (Tinting k) = Tinting (fmap g . k . (. (. f)))
instance Choice (Tinting a b) where
  left' (Tinting k) =
    Tinting (fmap Left . k . (. (\f -> either f (const Nothing))))
  right' (Tinting k) =
    Tinting (fmap Right . k . (. (\f -> either (const Nothing) f)))
instance Cochoice (Tinting a b) where
  unleft (Tinting k)
    = Tinting $ catMaybes
    . fmap (either Just (const Nothing))
    . k . (. (. Left))
  unright (Tinting k)
    = Tinting $ catMaybes
    . fmap (either (const Nothing) Just)
    . k . (. (. Right))
instance Monoidal1 (Tinting a b)
instance Monoidal (Tinting a b)
instance Distributor1 (Tinting a b)
instance Alternator1 (Tinting a b)
instance Filtrator (Tinting a b)
instance Tokenized a b (Tinting a b) where
  anyToken = Tinting ($ Just)

runTinting
  :: (Alternator p, Filtrator p)
  => Tinting a b s t
  -> ((s -> Maybe a) -> p a b)
  -> p s t
runTinting (Tinting k) f =
  unWrapP . k $ \sa -> WrapP (dimapMaybe sa Just (f sa))

type ATint s t a b =
  Tinting a b a (Maybe b) -> Tinting a b s (Maybe t)

withTint :: ATint s t a b -> (Tinting a b s t -> r) -> r
withTint tnt k = k (catMaybes (tnt (Just <$> anyToken)))

mapTint :: (Alternator p, Filtrator p) => ATint s t a b -> p a b -> p s t
mapTint mon p = withTint mon $ \eye ->
  runTinting eye $ \_ -> p

-- cloneTint :: ATint s t a b -> Tint s t a b
-- cloneTint tnt = unWrapPf . mapTint tnt . WrapPf
