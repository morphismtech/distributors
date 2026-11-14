{- |
Module      : Control.Lens.Bifocal
Description : bifocals
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Control.Lens.Bifocal
  ( -- * Bifocal
    Bifocal
  , ABifocal
  , Spectacle (..), runSpectacle, spectacle, withSpectacle
  , Binocular (..), runBinocular
    -- * Applicator
  , (>?<*)
    -- * Combinators
  , bifocal
  , withBifocal
  , cloneBifocal
  , crossBifocal
  , altBifocal
  , orBifocal
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.Internal.Profunctor
import Control.Lens.PartialIso
import Control.Monad ((>=>))
import Data.Monoid.Disjunctive (DisjunctiveMonoid (..))
import Data.Profunctor
import Data.Profunctor.Distributor
import Data.Profunctor.Monoidal ((>*<))
import Data.Profunctor.Monoidal.Cocartesian
import Data.Profunctor.Filtrator
import Data.Traversable.Homogeneous
import Data.Void
import GHC.Generics (Par1 (..), U1 (..), V1, (:*:) (..), (:+:) (..), (:.:) (..))
import Witherable

-- $setup
-- >>> import Control.Lens (_Just, _Left, _Right)
-- >>> import Control.Lens.PartialIso (clonePartialIso, satisfied)
-- >>> import Control.Lens.Prismoid (atLeast)
-- >>> import Data.Bifunctor.Joker (Joker (..))
-- >>> import Data.Char (isDigit, digitToInt)
-- >>> import Text.ParserCombinators.ReadP (readP_to_S, satisfy)

{- | `Bifocal`s are bidirectional parser optics.
`Control.Lens.Prismoid.Prismoid` ∪ `Control.Lens.PartialIso.PartialIso` ⊂ `Bifocal`,

so every `Control.Lens.Iso.Iso`, `Control.Lens.Prism.Prism`,
`Control.Lens.PartialIso.filterPrism`, `Control.Lens.Monocle.Monocle`,
`Control.Lens.Comonocle.Comonocle` & `Control.Lens.Diopter.Diopter`
is a `Bifocal` too.

`Bifocal`s are isomorphic to t'Spectacle's, by `Homogeneous` shapes,
& to t'Binocular's, by partial probes.
-}
type Bifocal s t a b = forall p f.
  (Alternator p, Applicative f, Filterable f)
    => p a (f b) -> p s (f t)

{- | `ABifocal` is monomorphically a `Bifocal`.

> prop> Bifocal s t a b ⊂ ABifocal s t a b
-}
type ABifocal s t a b =
  Spectacle a b a (Maybe b) -> Spectacle a b s (Maybe t)

{- | Build a `Bifocal` from a concrete t'Binocular'. -}
bifocal :: Binocular a b s t -> Bifocal s t a b
bifocal bif = unwrapPafb . runBinocular bif . WrapPafb

{- | Action of a `Bifocal` on partial `Alternator`s,
applying it directly at the `Alternator`, without converting it
to a concrete form, so the `Alternator`'s own methods,
like `someP` & `optionP`, act as they are, failing to build by
the `Alternator`'s `Filtrator`.
Clone `ABifocal` to apply it, by @`cloneBifocal` bif >?<* p@.

> prop> prsm >?<* p = prsm Control.Lens.Prismoid.>?* p
> prop> pat >?<* p = pat Control.Lens.PartialIso.>?< p

>>> let digits = runJoker (atLeast 1 >?<* Joker (satisfy isDigit))
>>> [ds | (ds, "") <- readP_to_S digits "123"]
["123"]
>>> let evenDigit = runJoker (satisfied even >?<* Joker (digitToInt <$> satisfy isDigit))
>>> [(d, rest) | (d, rest) <- readP_to_S evenDigit "41"]
[(4,"1")]
-}
(>?<*)
  :: (Alternator p, Filtrator p)
  => Bifocal s t a b -> p a b -> p s t
bif >?<* p = catMaybes (bif (rmap Just p))
infixl 4 >?<*

{- | Clone `ABifocal` so that you can reuse the same
monomorphically typed `Bifocal` for different purposes.
-}
cloneBifocal :: ABifocal s t a b -> Bifocal s t a b
cloneBifocal bif = withSpectacle bif $ \match build ->
  spectacle (Spectacle match build)

{- | Construct a `Bifocal` on pairs from components, with the same foci.

>>> withSpectacle (crossBifocal _Just _Just) $ \match build -> (match (Just 1, Just 2) >>= build . fmap negate, match (Just 1, Nothing) >>= build)
(Just (Just (-1),Just (-2)),Nothing)
-}
crossBifocal
  :: ABifocal s t a b
  -> ABifocal u v a b
  -> Bifocal (s,u) (t,v) a b
crossBifocal x y p =
  rmap (uncurry (liftA2 (,))) (cloneBifocal x p >*< cloneBifocal y p)

{- | Construct a `Bifocal` on `Either`s from components, with the same foci.

>>> withSpectacle (altBifocal _Just _Just) $ \match build -> (match (Left (Just 'x')) >>= build . fmap succ, match (Right Nothing) >>= build)
(Just (Left (Just 'y')),Nothing)
-}
altBifocal
  :: ABifocal s t a b
  -> ABifocal u v a b
  -> Bifocal (Either s u) (Either t v) a b
altBifocal x y p = rmap (either (fmap Left) (fmap Right))
  (cloneBifocal x p >+< cloneBifocal y p)

{- | Disjoin two `Bifocal`s on the same source, by `>|<`.

> prop> orBifocal x falseOptic = cloneBifocal x
> prop> orBifocal falseOptic y = cloneBifocal y

>>> withSpectacle (orBifocal _Left _Right) $ \match build -> (match (Left 'x') >>= build . fmap succ, match (Right 'x') >>= build . fmap succ)
(Just (Left 'y'),Just (Right 'y'))
-}
orBifocal
  :: ABifocal s t a b
  -> ABifocal s t a b
  -> Bifocal s t a b
orBifocal x y p = cloneBifocal x p >|< cloneBifocal y p

{- | Run `ABifocal` over an `Alternative` & `Filterable`,
by partial probes. -}
withBifocal
  :: (Alternative f, Filterable f)
  => ABifocal s t a b -> ((s -> Maybe a) -> f b) -> f t
withBifocal bif = unBinocular (cloneBifocal bif >?<* Binocular ($ Just))

{- | t'Binocular' is a secondary concrete representation of `Bifocal`s,
by partial probes, each of which matches from the source anew. -}
newtype Binocular a b s t = Binocular
  { unBinocular
      :: forall f. (Alternative f, Filterable f)
      => ((s -> Maybe a) -> f b) -> f t
  }
instance Profunctor (Binocular a b) where
  dimap f g (Binocular k) = Binocular $ fmap g . k . (. (. f))
instance Functor (Binocular a b s) where fmap = rmap
instance Applicative (Binocular a b s) where
  pure t = Binocular (pure (pure t))
  Binocular x <*> Binocular y = Binocular (liftA2 (<*>) x y)
instance Alternative (Binocular a b s) where
  empty = Binocular (pure empty)
  Binocular x <|> Binocular y = Binocular (liftA2 (<|>) x y)
  many = lmap repeat . manyP
  some = lmap repeat . someP
instance DisjunctiveMonoid (Binocular a b s t)
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
instance CocartesianMonoidal (Binocular a b)
instance Distributor (Binocular a b)
instance CocartesianChoice (Binocular a b)
instance Alternator (Binocular a b)
instance Filtrator (Binocular a b)

{- | Run a t'Binocular' on a partial `Distributor`. -}
runBinocular
  :: (Alternator p, Filtrator p)
  => Binocular a b s t
  -> p a b -> p s t
runBinocular (Binocular k) p = k $ \f -> dimapMaybe f Just p

{- | t'Spectacle' provides an efficient
concrete representation of `Bifocal`s, by `Homogeneous` shapes, matching partially forwards
& building partially backwards, a
t'Control.Lens.Prismoid.Prismatoid' which may also fail to build.
-}
data Spectacle a b s t where
  Spectacle
    :: Homogeneous h
    => (s -> Maybe (h a))
    -> (h b -> Maybe t)
    -> Spectacle a b s t
instance Profunctor (Spectacle a b) where
  dimap f' g' (Spectacle f g) = Spectacle (f . f') (fmap g' . g)
instance Functor (Spectacle a b s) where fmap = rmap
instance Applicative (Spectacle a b s) where
  pure t = Spectacle (const (Just U1)) (const (Just t))
  liftA2 h (Spectacle f0 g0) (Spectacle f1 g1) = Spectacle
    (\s -> liftA2 (:*:) (f0 s) (f1 s))
    (\(x :*: y) -> liftA2 h (g0 x) (g1 y))
  (<*>) = liftA2 id
instance Alternative (Spectacle a b s) where
  empty = Spectacle (const Nothing) (\(v :: V1 b) -> case v of {})
  Spectacle f0 g0 <|> Spectacle f1 g1 = Spectacle
    (\s -> (L1 <$> f0 s) <|> (R1 <$> f1 s))
    (\case {L1 x -> g0 x; R1 y -> g1 y})
instance DisjunctiveMonoid (Spectacle a b s t)
instance Filterable (Spectacle a b s) where
  mapMaybe h (Spectacle f g) = Spectacle f (g >=> h)
instance CocartesianMonoidal (Spectacle a b) where
  zeroP = Spectacle absurd (\(v :: V1 b) -> case v of {})
  Spectacle f0 g0 >+< Spectacle f1 g1 = Spectacle
    (either (fmap L1 . f0) (fmap R1 . f1))
    (\case {L1 x -> Left <$> g0 x; R1 y -> Right <$> g1 y})
instance Choice (Spectacle a b) where
  left' = alternate . Left
  right' = alternate . Right
instance Cochoice (Spectacle a b) where
  unleft (Spectacle f g) =
    Spectacle (f . Left) (g >=> either Just (const Nothing))
  unright (Spectacle f g) =
    Spectacle (f . Right) (g >=> either (const Nothing) Just)
instance CocartesianChoice (Spectacle a b) where
  alternate = \case
    Left (Spectacle f g) ->
      Spectacle (either f (const Nothing)) (fmap Left . g)
    Right (Spectacle f g) ->
      Spectacle (either (const Nothing) f) (fmap Right . g)
instance Distributor (Spectacle a b) where
  optionalP (Spectacle f g) =
    Spectacle (fmap Comp1 . traverse f) (traverse g . unComp1)
  manyP (Spectacle f g) =
    Spectacle (fmap Comp1 . traverse f) (traverse g . unComp1)
instance Alternator (Spectacle a b)
instance Filtrator (Spectacle a b)

{- | Run a t'Spectacle' on a partial `Distributor`,
failing by `falseP` where it doesn't match,
& by `mapMaybe` where it doesn't build. -}
runSpectacle
  :: (Alternator p, Filtrator p)
  => Spectacle a b s t -> p a b -> p s t
runSpectacle (Spectacle f g) p =
  dialt (maybe (Left ()) Right . f) id id falseP (mapMaybe g (homogeneously p))

{- | Build a `Bifocal` from a t'Spectacle'. -}
spectacle :: Spectacle a b s t -> Bifocal s t a b
spectacle sp = unwrapPafb . runSpectacle sp . WrapPafb

{- | Convert `ABifocal` to the pair of functions that characterize it,
matching into & building from a `Homogeneous` shape.

>>> withSpectacle (clonePartialIso _Just) $ \match build -> (match Nothing >>= build, match (Just 'x') >>= build . fmap succ)
(Nothing,Just (Just 'y'))
-}
withSpectacle
  :: ABifocal s t a b
  -> (forall h. Homogeneous h => (s -> Maybe (h a)) -> (h b -> Maybe t) -> r)
  -> r
withSpectacle bif k =
  case catMaybes (bif (Just <$> Spectacle (Just . Par1) (Just . unPar1))) of
    Spectacle f g -> k f g
