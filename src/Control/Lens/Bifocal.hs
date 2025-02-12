{- |
Module      : Control.Lens.Bifocal
Description : bifocals
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Control.Lens.Bifocal
  ( Bifocal
  , Bifocal'
  , ABifocal
  , ABifocal'
  , Diopter
  , Prismoid
  , Filtroid
  , bifocal
  , mapBifocal
  , cloneBifocal
  , withBifocal
  , optioned
  , manied
  , somed
  , lefted
  , righted
  , unlefted
  , unrighted
  , chainedl
  , chainedr
  , Binocular (..), runBinocular
  ) where

import Control.Applicative
import Control.Lens.Internal.Profunctor
import Control.Lens.PartialIso
import Data.Bool
import Data.Profunctor
import Data.Profunctor.Distributor
import Witherable

type Bifocal s t a b = forall p f.
  (Alternator p, Filtrator p, Alternative f, Filterable f)
    => p a (f b) -> p s (f t)

type Bifocal' s a = Bifocal s s a a

type ABifocal s t a b =
  Binocular a b a (Maybe b) -> Binocular a b s (Maybe t)

type ABifocal' s a = ABifocal s s a a

type Diopter s t a b = forall p f.
  (Distributor p, Applicative f)
    => p a (f b) -> p s (f t)

type Prismoid s t a b = forall p f.
  (Alternator p, Alternative f)
    => p a (f b) -> p s (f t)

type Filtroid s t a b = forall p f.
  (Filtrator p, Filterable f)
    => p a (f b) -> p s (f t)

bifocal :: Binocular a b s t -> Bifocal s t a b
bifocal bif = unwrapPafb . runBinocular bif . WrapPafb

mapBifocal
  :: (Alternator p, Filtrator p)
  => ABifocal s t a b -> p a b -> p s t
mapBifocal bif p = withBifocal bif $ \f -> dimapMaybe f Just p

cloneBifocal :: ABifocal s t a b -> Bifocal s t a b
cloneBifocal bif = unwrapPafb . mapBifocal bif . WrapPafb

optioned :: Diopter (Maybe a) (Maybe b) a b
optioned = unwrapPafb . optionalP . WrapPafb

manied :: Diopter [a] [b] a b
manied = unwrapPafb . manyP . WrapPafb

somed :: Prismoid [a] [b] a b
somed = unwrapPafb . someP . WrapPafb

lefted :: Prismoid (Either a c) (Either b d) a b
lefted = unwrapPafb . alternate . Left . WrapPafb

righted :: Prismoid (Either c a) (Either d b) a b
righted = unwrapPafb . alternate . Right . WrapPafb

unlefted :: Filtroid a b (Either a c) (Either b d)
unlefted = unwrapPafb . fst . filtrate . WrapPafb

unrighted :: Filtroid a b (Either c a) (Either d b)
unrighted = unwrapPafb . snd . filtrate . WrapPafb

chainedl :: APartialIso a b (a,a) (b,b) -> Bifocal a b a b
chainedl pat = unwrapPafb . chainl1 pat noSep . WrapPafb

chainedr :: APartialIso a b (a,a) (b,b) -> Bifocal a b a b
chainedr pat = unwrapPafb . chainr1 pat noSep . WrapPafb

withBifocal
  :: (Filterable f, Alternative f)
  => ABifocal s t a b -> ((s -> Maybe a) -> f b) -> f t
withBifocal bif = unBinocular (catMaybes (bif (Just <$> anyToken)))

newtype Binocular a b s t = Binocular
  { unBinocular
      :: forall f. (Filterable f, Alternative f)
      => ((s -> Maybe a) -> f b) -> f t
  }
instance Tokenized a b (Binocular a b) where
  anyToken = Binocular ($ Just)
instance Profunctor (Binocular a b) where
  dimap f g (Binocular k) = Binocular $ fmap g . k . (. (. f))
instance Functor (Binocular a b s) where fmap = rmap
instance Applicative (Binocular a b s) where
  pure t = Binocular (pure (pure t))
  Binocular x <*> Binocular y = Binocular (liftA2 (<*>) x y)
instance Alternative (Binocular a b s) where
  empty = Binocular (pure empty)
  Binocular x <|> Binocular y = Binocular (liftA2 (<|>) x y)
instance Filterable (Binocular a b s) where
  mapMaybe f (Binocular k) = Binocular (mapMaybe f . k)
  catMaybes (Binocular k) = Binocular (catMaybes . k)
instance Choice (Binocular a b) where
  left' (Binocular k)
    = Binocular $ fmap Left
    . k . (. (\f -> either f (const Nothing)))
  right' (Binocular k)
    = Binocular $ fmap Right
    . k . (. (\f -> either (const Nothing) f))
instance Cochoice (Binocular a b) where
  unleft (Binocular k)
    = Binocular $ catMaybes
    . fmap (either Just (const Nothing))
    . k . (. (. Left))
  unright (Binocular k)
    = Binocular $ catMaybes
    . fmap (either (const Nothing) Just)
    . k . (. (. Right))
instance Distributor (Binocular a b)
instance Alternator (Binocular a b)
instance Filtrator (Binocular a b)

runBinocular
  :: (Alternator p, Filtrator p)
  => Binocular a b s t
  -> p a b -> p s t
runBinocular (Binocular k) p = k $ \f -> dimapMaybe f Just p
