module Control.Lens.PartialIso
  ( -- * choice and cochoice profunctors
    dimapMaybe, alternate, discriminate, mapMaybeP, catMaybesP
    -- * partial isomorphisms
  , PartialIso, PartialIso', APartialIso, APartialIso'
  , partialIso, withPartialIso, clonePartialIso
  , coPartialIso, crossPartialIso, altPartialIso
  , (>?), (?<), (>?<)
  , _Guard, _Normal, _M2E, iterating
    -- * types
  , PartialExchange (PartialExchange)
  ) where

import Control.Applicative
import Control.Lens
import Control.Monad
import Data.Profunctor
import Witherable

{- | A `Choice` and `Cochoice` profunctor
exhibits an action of partial isomorphisms.

prop> i >?< p = withPartialIso i $ \f g -> dimapMaybe f g p

`dimapMaybe` is the structural morphism for `Choice` and `Cochoice`
profunctors. It's comparable to the `mapMaybe` method
of the `Filterable` class.
-}
dimapMaybe
  :: (Choice p, Cochoice p)
  => (s -> Maybe a) -> (b -> Maybe t)
  -> p a b -> p s t
dimapMaybe f g =
  let
    m2e h = view _M2E . h
    fg = dimap (>>= m2e f) (>>= m2e g)
  in
    unright . fg . right'

{- | `Choice` and `Cochoice` profunctors
generalize the `Choice` methods
with the `alternate` function.

prop> left' = alternate . Left
prop> right' = alternate . Right

`alternate` has less general constraint
but a more general type,
than `left'` `|||` `right'`.

>>> :type left' ||| right'
left' ||| right'
  :: Choice p =>
     Either (p a a) (p c c) -> p (Either a c) (Either a c)
-}
alternate
  :: (Choice p, Cochoice p)
  => Either (p a b) (p c d)
  -> p (Either a c) (Either b d)
alternate (Left p) =
  dimapMaybe (either Just (pure Nothing)) (Just . Left) p
alternate (Right p) =
  dimapMaybe (either (pure Nothing) Just) (Just . Right) p

{-| `Choice` and `Cochoice` profunctors
generalize the `Cochoice` methods
with the `discriminate` function.

prop> unleft = fst . discriminate
prop> unright = snd . discriminate

`discriminate` has less general constraint
but a more general type,
than `unleft` `&&&` `unright`.

>>> :type unleft &&& unright
unleft &&& unright
  :: Cochoice p => p (Either a d) (Either a d) -> (p a a, p d d)
-}
discriminate
  :: (Choice p, Cochoice p)
  => p (Either a c) (Either b d)
  -> (p a b, p c d)
discriminate p =
  ( dimapMaybe (Just . Left) (either Just (pure Nothing)) p
  , dimapMaybe (Just . Right) (either (pure Nothing) Just) p
  )

mapMaybeP
  :: (Choice p, Cochoice p)
  => (b -> Maybe t)
  -> p a b -> p a t
mapMaybeP = dimapMaybe Just

catMaybesP
  :: (Choice p, Cochoice p)
  => p a (Maybe b) -> p a b
catMaybesP = mapMaybeP id

data PartialExchange a b s t =
  PartialExchange (s -> Maybe a) (b -> Maybe t)
instance Semigroup (PartialExchange a b s t) where
  PartialExchange f g <> PartialExchange f' g' =
    PartialExchange (\s -> f s <|> f' s) (\b -> g b <|> g' b)    
instance Monoid (PartialExchange a b s t) where
  mempty = PartialExchange nope nope where
    nope _ = Nothing
instance Functor (PartialExchange a b s) where fmap = rmap
instance Filterable (PartialExchange a b s) where
  mapMaybe = mapMaybeP
instance Monoid a => Applicative (PartialExchange a b s) where
  pure t = PartialExchange (\_ -> mempty) (\_ -> Just t)
  PartialExchange f' g' <*> PartialExchange f g = PartialExchange
    (\s -> (<>) <$> f' s <*> f s)
    (\b -> g' b <*> g b)
instance Monoid a => Alternative (PartialExchange a b s) where
  empty = mempty
  (<|>) = (<>)
instance Profunctor (PartialExchange a b) where
  dimap f' g' (PartialExchange f g) =
    PartialExchange (f . f') (fmap g' . g)
instance Choice (PartialExchange a b) where
  left' (PartialExchange f g) =
    PartialExchange (either f (pure Nothing)) ((Left <$>) . g)
  right' (PartialExchange f g) =
    PartialExchange (either (pure Nothing) f) ((Right <$>) . g)
instance Cochoice (PartialExchange a b) where
  unleft (PartialExchange f g) =
    PartialExchange (f . Left) (either Just (pure Nothing) <=< g)
  unright (PartialExchange f g) =
    PartialExchange (f . Right) (either (pure Nothing) Just <=< g)

{- | `PartialIso` is a first class inexhaustive pattern,
similar to how 'Prism' is a first class exhaustive pattern.
`APrism` can be a `PartialIso`.
Thus, `AnIso` can be a `PartialIso`.

`PartialIso`s are a functionalization of `PartialExchange`s.

>>> :{
let
  fromPartialIso :: APartialIso s t a b -> PartialExchange a b s t
  fromPartialIso i = withPartialIso i PartialExchange
  toPartialIso :: PartialExchange a b s t -> PartialIso s t a b
  toPartialIso (PartialExchange f g) = partialIso f g
:}
prop> id = fromPartialIso . toPartialIso
prop> id = toPartialIso . fromPartialIso
-}
type PartialIso s t a b = forall p f.
  (Choice p, Cochoice p, Applicative f, Filterable f)
    => p a (f b) -> p s (f t)

{- |
A simple `PartialIso'` @s a@ is an identification of
a subset of `s` with a subset of `a`.

Given a simple `PartialIso'` @partialIso f g@.

prop> Just = f <=< g
prop> Just = g <=< f

These are left and right inverse laws for proper `PartialIso'`s.
However, sometimes an improper `PartialIso'` will be useful.
For an improper `PartialIso'`, only the left inverse law holds.

prop> Just = f <=< g

For the improper `PartialIso'`, @g <=< f@ will be regarded
as a normalization within some equivalence class of terms.
-}
type PartialIso' s a = PartialIso s s a a

type APartialIso s t a b =
  PartialExchange a b a (Maybe b) -> PartialExchange a b s (Maybe t)

type APartialIso' s a = APartialIso s s a a

partialIso :: (s -> Maybe a) -> (b -> Maybe t) -> PartialIso s t a b
partialIso f g =
  unright . iso (view _M2E . f =<<) (mapMaybe g) . right'

withPartialIso
  :: APartialIso s t a b
  -> ((s -> Maybe a) -> (b -> Maybe t) -> r)
  -> r
withPartialIso i k =
  case i (PartialExchange Just (Just . Just)) of
    PartialExchange f g -> k f (join . g)

clonePartialIso
  :: APartialIso s t a b
  -> PartialIso s t a b
clonePartialIso i = withPartialIso i $ \f g -> partialIso f g

coPartialIso
  :: APartialIso b a t s
  -> PartialIso s t a b
coPartialIso i =
  withPartialIso i $ \f g -> partialIso g f

iterating :: APartialIso a b a b -> Iso a b a b
iterating i = withPartialIso i $ \f g ->
  iso (iter f) (iter g) where
    iter h state = maybe state (iter h) (h state)

crossPartialIso
  :: APartialIso s t a b
  -> APartialIso u v c d
  -> PartialIso (s,u) (t,v) (a,c) (b,d)
crossPartialIso x y =
  withPartialIso x $ \e f ->
  withPartialIso y $ \g h ->
    partialIso
      (\(s,u) -> (,) <$> e s <*> g u)
      (\(t,v) -> (,) <$> f t <*> h v)

altPartialIso
  :: APartialIso s t a b
  -> APartialIso u v c d
  -> PartialIso
      (Either s u) (Either t v)
      (Either a c) (Either b d)
altPartialIso x y =
  withPartialIso x $ \e f ->
  withPartialIso y $ \g h ->
    partialIso
      (either ((Left <$>) . e) ((Right <$>) . g))
      (either ((Left <$>) . f) ((Right <$>) . h)) 

(>?)
  :: Choice p
  => APrism s t a b
  -> p a b
  -> p s t
i >? p = withPrism i $ \f g ->
  dimap g (either id f) (right' p)
infixr 4 >?

(?<)
  :: Cochoice p
  => APrism b a t s
  -> p a b
  -> p s t
i ?< p = withPrism i $ \f g ->
  unright (dimap (either id f) g p)
infixr 4 ?<

(>?<)
  :: (Choice p, Cochoice p)
  => APartialIso s t a b
  -> p a b
  -> p s t
i >?< p =
  withPartialIso i $ \f g -> dimapMaybe f g p
infixr 4 >?<

_Guard :: (a -> Bool) -> PartialIso' a a
_Guard f = partialIso satiate satiate where
  satiate a = if f a then Just a else Nothing

_Normal :: a -> Iso' a ()
_Normal a = iso (const ()) (const a) where

_M2E :: Iso (Maybe a) (Maybe b) (Either () a) (Either () b)
_M2E = iso (maybe (Left ()) Right) (either (pure Nothing) Just)
