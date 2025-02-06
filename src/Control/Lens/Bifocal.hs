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
  , cloneBifocal
  , mapBifocal
  , withBifocal
  , Binocular (..), runBinocular
  ) where

import Control.Applicative
import Control.Lens.Monocle
import Control.Lens.Token
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

cloneBifocal :: ABifocal s t a b -> Bifocal s t a b
cloneBifocal bif = unWrapPF . mapBifocal bif . WrapPF

mapBifocal
  :: (Alternator p, Filtrator p)
  => ABifocal s t a b -> p a b -> p s t
mapBifocal bif = withBifocal bif . flip runBinocular . const

_Optional :: Bifocal (Maybe a) (Maybe b) a b
_Optional = unWrapPF . optionalP . WrapPF

_Many :: Bifocal [a] [b] a b
_Many = unWrapPF . manyP . WrapPF

_Some :: Bifocal [a] [b] a b
_Some = unWrapPF . someP . WrapPF

withBifocal :: ABifocal s t a b -> (Binocular a b s t -> r) -> r
withBifocal bif k = k (catMaybes (bif (Just <$> anyToken)))

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
  :: ( Choice p
     , Cochoice p
     , forall x. Alternative (p x)
     , forall x. Filterable (p x)
     )
  => Binocular a b s t
  -> ((s -> Maybe a) -> p a b)
  -> p s t
runBinocular (Binocular k) f = k $ \sa -> dimapMaybe sa Just (f sa)
