{-|
Module      : Data.Profunctor.Distributor
Description : lax monoidal & distributive profunctors
Copyright   : (C) 2025 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Data.Profunctor.Distributor
  ( Monoidal, oneP, (>*<), dimap2, (>*), (*<), replicateP, foreverP, meander
  , Distributor (zeroP, (>+<), optionalP, manyP), dialt
  , Alternator (alternate, someP)
  , Filtrator (filtrate)
  , Tokenized (anyToken), token, tokens, satisfy, restOfTokens, endOfTokens
  , SepBy (..), sepBy, atLeast0, atLeast1, chainl1, chainr1
  ) where

import Control.Applicative hiding (WrappedArrow)
import Control.Applicative qualified as Ap (WrappedArrow)
import Control.Arrow
import Control.Lens hiding (chosen)
import Control.Lens.Internal.Bazaar
import Control.Lens.Internal.Context
import Control.Lens.Internal.Iso
import Control.Lens.Internal.Prism
import Control.Lens.Internal.Profunctor
import Control.Lens.PartialIso
import Data.Bifunctor.Clown
import Data.Bifunctor.Joker
import Data.Bifunctor.Product
import Data.Distributive
import Data.Functor.Adjunction
import Data.Functor.Compose
import Data.Functor.Contravariant.Divisible
import Data.Profunctor hiding (WrappedArrow)
import Data.Profunctor qualified as Pro (WrappedArrow)
import Data.Profunctor.Composition
import Data.Profunctor.Monad
import Data.Profunctor.Yoneda
import Data.Void
import Witherable

type Monoidal p = (Profunctor p, forall x. Applicative (p x))

oneP :: Monoidal p => p () ()
oneP = pure ()

(>*<) :: Monoidal p => p a b -> p c d -> p (a,c) (b,d)
(>*<) = dimap2 fst snd (,)
infixr 6 >*<

dimap2
  :: Monoidal p
  => (s -> a)
  -> (s -> c)
  -> (b -> d -> t)
  -> p a b -> p c d -> p s t
dimap2 f g h p q = liftA2 h (lmap f p) (lmap g q)

(>*) :: Monoidal p => p () c -> p a b -> p a b
x >* y = lmap (const ()) x *> y
infixl 5 >*

(*<) :: Monoidal p => p a b -> p () c -> p a b
x *< y = x <* lmap (const ()) y
infixl 5 *<

foreverP :: Monoidal p => p () c -> p a b
foreverP a = let a' = a >* a' in a'

-- thanks to Fy on Monoidal Café Discord
replicateP
  :: (Monoidal p, Traversable t, Distributive t)
  => p a b -> p (t a) (t b)
replicateP p = traverse (\f -> lmap f p) (distribute id)

meander
  :: forall p s t a b. (Monoidal p, Choice p, Strong p) -- should redundant Strong stay or go?
  => ATraversal s t a b -> p a b -> p s t
meander f = dimap (f sell) iextract . trav
  where
    trav :: p u v -> p (Bazaar (->) u w x) (Bazaar (->) v w x)
    trav q = mapIso _Bazaar $ right' (q >*< trav q)

class Monoidal p => Distributor p where

  zeroP :: p Void Void
  default zeroP :: Alternator p => p Void Void
  zeroP = empty

  (>+<) :: p a b -> p c d -> p (Either a c) (Either b d)
  default (>+<)
    :: Alternator p
    => p a b -> p c d -> p (Either a c) (Either b d)
  x >+< y = alternate (Left x) <|> alternate (Right y)
  infixr 3 >+<

  optionalP :: p a b -> p (Maybe a) (Maybe b)
  optionalP = dialt (maybe (Left ()) Right) (const Nothing) Just oneP

  manyP :: p a b -> p [a] [b]
  manyP p = dialt unlist list0 list1 oneP (p >*< manyP p)

instance Distributor (->) where
  zeroP = id
  (>+<) = (+++)
instance Monoid s => Distributor (Forget s) where
  zeroP = Forget absurd
  Forget kL >+< Forget kR = Forget (either kL kR)
instance Decidable f => Distributor (Clown f) where
  zeroP = Clown lost
  Clown x >+< Clown y = Clown (chosen x y)
instance Alternative f => Distributor (Joker f) where
  zeroP = Joker empty
  Joker x >+< Joker y = Joker (Left <$> x <|> Right <$> y)
instance (Distributor p, Applicative f)
  => Distributor (WrappedPafb f p) where
    zeroP = WrapPafb (rmap pure zeroP)
    WrapPafb x >+< WrapPafb y = WrapPafb $
      dialt id (fmap Left) (fmap Right) x y
    -- manyP
    -- optionalP

instance Applicative f => Distributor (Star f) where
  zeroP = Star absurd
  Star f >+< Star g =
    Star (either (fmap Left . f) (fmap Right . g))
deriving via (Star m) instance Monad m => Distributor (Kleisli m)
instance Adjunction f u => Distributor (Costar f) where
  zeroP = Costar unabsurdL
  Costar f >+< Costar g = Costar (bimap f g . cozipL)
-- instance (Applicative f, Distributor p)
--   => Distributor (Tannen f p) where
--     zeroP = Tannen (pure zeroP)
--     Tannen x >+< Tannen y = Tannen ((>+<) <$> x <*> y)
-- instance (Applicative f, Distributor p)
--   => Distributor (Cayley f p) where
--     zeroP = Cayley (pure zeroP)
--     Cayley x >+< Cayley y = Cayley ((>+<) <$> x <*> y)
-- instance (Adjunction f u, Applicative g, Distributor p)
--   => Distributor (Biff p f g) where
--     zeroP = Biff (dimap unabsurdL absurd zeroP)
--     Biff x >+< Biff y = Biff $ dimap
--       cozipL
--       (either (Left <$>) (Right <$>))
--       (x >+< y)
instance (ArrowZero p, ArrowChoice p)
  => Distributor (Pro.WrappedArrow p) where
    zeroP = zeroArrow
    (>+<) = (+++)
deriving via (Pro.WrappedArrow p)
  instance (ArrowZero p, ArrowChoice p)
    => Distributor (Ap.WrappedArrow p)
instance (Distributor p, Distributor q)
  => Distributor (Procompose p q) where
    zeroP = Procompose zeroP zeroP
    Procompose xL yL >+< Procompose xR yR =
      Procompose (xL >+< xR) (yL >+< yR)
instance (Distributor p, Distributor q)
  => Distributor (Product p q) where
    zeroP = Pair zeroP zeroP
    Pair x0 y0 >+< Pair x1 y1 = Pair (x0 >+< x1) (y0 >+< y1)
instance Distributor p => Distributor (Yoneda p) where
  zeroP = proreturn zeroP
  ab >+< cd = proreturn (proextract ab >+< proextract cd)
instance Distributor p => Distributor (Coyoneda p) where
  zeroP = proreturn zeroP
  ab >+< cd = proreturn (proextract ab >+< proextract cd)

dialt
  :: Distributor p
  => (s -> Either a c)
  -> (b -> t)
  -> (d -> t)
  -> p a b -> p c d -> p s t
dialt f g h p q = dimap f (either g h) (p >+< q)

class (Choice p, Distributor p, forall x. Alternative (p x))
  => Alternator p where

    alternate
      :: Either (p a b) (p c d)
      -> p (Either a c) (Either b d)
    default alternate
      :: Cochoice p
      => Either (p a b) (p c d)
      -> p (Either a c) (Either b d)
    alternate =
      dimapMaybe (either Just (pure Nothing)) (Just . Left)
      |||
      dimapMaybe (either (pure Nothing) Just) (Just . Right)

    someP :: p a b -> p [a] [b]
    someP p = dimap unlist (either list0 list1) (right' (p >*< manyP p))

instance (Alternator p, Alternative f)
  => Alternator (WrappedPafb f p) where
    alternate =
      let
        f = WrapPafb
          . rmap (either (fmap Left) pure)
          . alternate
          . Left
          . unwrapPafb
        g = WrapPafb
          . rmap (either pure (fmap Right))
          . alternate
          . Right
          . unwrapPafb
      in
        either f g
    -- someP

unlist :: [a] -> Either () (a, [a])
unlist [] = Left ()
unlist (a:as) = Right (a,as)

list0 :: () -> [a]
list0 _ = []

list1 :: (a,[a]) -> [a]
list1 = uncurry (:)

class (Cochoice p, forall x. Filterable (p x))
  => Filtrator p where

    filtrate
      :: p (Either a c) (Either b d)
      -> (p a b, p c d)
    default filtrate
      :: Choice p
      => p (Either a c) (Either b d)
      -> (p a b, p c d)
    filtrate =
      dimapMaybe (Just . Left) (either Just (pure Nothing))
      &&&
      dimapMaybe (Just . Right) (either (pure Nothing) Just)

instance (Filtrator p, Filterable f)
  => Filtrator (WrappedPafb f p) where
    filtrate (WrapPafb p) =
      let
        fL = Left . mapMaybe (either Just (const Nothing))
        fR = Right . mapMaybe (either (const Nothing) Just)
        (pL,_) = filtrate (rmap fL p)
        (_,pR) = filtrate (rmap fR p)
      in
        ( WrapPafb pL
        , WrapPafb pR
        )

-- Tokenized --

class Tokenized a b p | p -> a, p -> b where
  anyToken :: p a b
instance Tokenized a b (Identical a b) where
  anyToken = Identical
instance Tokenized a b (Exchange a b) where
  anyToken = Exchange id id
instance Tokenized a b (Market a b) where
  anyToken = Market id Right
instance Tokenized a b (PartialExchange a b) where
  anyToken = PartialExchange Just Just

token :: (Cochoice p, Eq c, Tokenized c c p) => c -> p () ()
token c = only c ?< anyToken

tokens :: (Cochoice p, Monoidal p, Eq c, Tokenized c c p) => [c] -> p () ()
tokens [] = oneP
tokens (c:cs) = token c *> tokens cs

satisfy :: (Choice p, Cochoice p, Tokenized c c p) => (c -> Bool) -> p c c
satisfy f = satisfied f >?< anyToken

restOfTokens :: (Distributor p, Tokenized c c p) => p [c] [c]
restOfTokens = manyP anyToken

endOfTokens :: (Cochoice p, Distributor p, Tokenized c c p) => p () ()
endOfTokens = _Empty ?< restOfTokens

-- SepBy --

{- | Used to parse multiple times, delimited by a `separateBy`,
a `beginBy`, and an `endBy`. -}
data SepBy p = SepBy
  { beginBy :: p () ()
  , endBy :: p () ()
  , separateBy :: p () ()
  }

{- | A default `SepBy` which can be modified by updating
`beginBy`, or `endBy` fields -}
sepBy :: Monoidal p => p () () -> SepBy p
sepBy = SepBy oneP oneP

atLeast0
  :: Distributor p
  => SepBy p -> p a b -> p [a] [b]
atLeast0 sep p =
  beginBy sep >* 
  dialt unlist list0 list1 oneP (p >*< manyP (separateBy sep >* p))
  *< endBy sep

atLeast1
  :: Alternator p
  => SepBy p -> p a b -> p [a] [b]
atLeast1 sep p = dimap unlist (either list0 list1)
  (right' (beginBy sep >* p >*< manyP (separateBy sep >* p) *< endBy sep))

chainl1
  :: (Alternator p, Filtrator p)
  => APartialIso a b (a,a) (b,b) -> SepBy p -> p a b -> p a b
chainl1 pat sep p =
  coPartialIso (difoldl (coPartialIso pat)) >?<
    beginBy sep >* p >*< manyP (separateBy sep >* p) *< endBy sep

chainr1
  :: (Alternator p, Filtrator p)
  => APartialIso a b (a,a) (b,b) -> SepBy p -> p a b -> p a b
chainr1 pat sep p =
  coPartialIso (difoldr (coPartialIso pat)) >?<
    beginBy sep >* manyP (p *< separateBy sep) >*< p *< endBy sep

-- FunList --

data FunList a b t
  = DoneFun t
  | MoreFun a (Bazaar (->) a b (b -> t))
instance Functor (FunList a b) where
  fmap f = \case
    DoneFun t -> DoneFun (f t)
    MoreFun a h -> MoreFun a (fmap (f .) h)
instance Applicative (FunList a b) where
  pure = DoneFun
  (<*>) = \case
    DoneFun t -> fmap t
    MoreFun a h -> \l ->
      MoreFun a (flip <$> h <*> view _FunList l)
instance Sellable (->) FunList where sell b = MoreFun b (pure id)
instance Bizarre (->) FunList where
  bazaar f = \case
    DoneFun t -> pure t
    MoreFun a l -> ($) <$> bazaar f l <*> f a

_FunList :: Iso
  (FunList a1 b1 t1) (FunList a2 b2 t2)
  (Bazaar (->) a1 b1 t1) (Bazaar (->) a2 b2 t2)
_FunList = iso fromFun toFun where
  toFun (Bazaar f) = f sell
  fromFun = \case
    DoneFun t -> pure t
    MoreFun a f -> ($) <$> f <*> sell a

_Bazaar :: Iso
  (Bazaar (->) a1 b1 t1) (Bazaar (->) a2 b2 t2)
  (Either t1 (a1, Bazaar (->) a1 b1 (b1 -> t1)))
  (Either t2 (a2, Bazaar (->) a2 b2 (b2 -> t2)))
_Bazaar = from _FunList . iso f g where
  f = \case
    DoneFun t -> Left t
    MoreFun a baz -> Right (a, baz)
  g = \case
    Left t -> DoneFun t
    Right (a, baz) -> MoreFun a baz

-- ORPHANAGE --

instance Monoid r => Applicative (Forget r a) where
  pure _ = Forget mempty
  Forget f <*> Forget g = Forget (f <> g)
instance Decidable f => Applicative (Clown f a) where
  pure _ = Clown conquer
  Clown x <*> Clown y = Clown (divide (id &&& id) x y)
deriving newtype instance Applicative f => Applicative (Joker f a)
instance (Profunctor p, Functor f)
  => Functor (WrappedPafb f p a) where fmap = rmap
deriving via Compose (p a) f instance
  (Monoidal p, Applicative f)
    => Applicative (WrappedPafb f p a)
deriving via Compose (p a) f instance
  (Profunctor p, forall x. Alternative (p x), Applicative f)
    => Alternative (WrappedPafb f p a)
deriving via Compose (p a) f instance
  (Profunctor p, forall x. Functor (p x), Filterable f)
    => Filterable (WrappedPafb f p a)
instance (Profunctor p, Filterable f)
  => Cochoice (WrappedPafb f p) where
    unleft (WrapPafb p) = WrapPafb $
      dimap Left (mapMaybe (either Just (const Nothing))) p
    unright (WrapPafb p) = WrapPafb $
      dimap Right (mapMaybe (either (const Nothing) Just)) p
instance (Closed p, Distributive f)
  => Closed (WrappedPafb f p) where
    closed (WrapPafb p) = WrapPafb (rmap distribute (closed p))
deriving via (Ap.WrappedArrow p x) instance Arrow p
  => Functor (Pro.WrappedArrow p x)
deriving via (Ap.WrappedArrow p x) instance Arrow p
  => Applicative (Pro.WrappedArrow p x)
deriving via (Pro.WrappedArrow p) instance Arrow p
  => Profunctor (Ap.WrappedArrow p)
instance (Monoidal p, Monoidal q)
  => Applicative (Procompose p q x) where
    pure b = Procompose (pure b) (pure b)
    Procompose wb aw <*> Procompose vb av = Procompose
      (dimap2 fst snd ($) wb vb)
      (liftA2 (,) aw av)
instance (Monoidal p, Monoidal q)
  => Applicative (Product p q x) where
    pure b = Pair (pure b) (pure b)
    Pair x0 y0 <*> Pair x1 y1 = Pair (x0 <*> x1) (y0 <*> y1)
-- instance (Applicative f, Monoidal p) => Monoidal (Tannen f p) where
--   oneP = Tannen (pure oneP)
--   Tannen x >*< Tannen y = Tannen ((>*<) <$> x <*> y)
-- instance (Applicative f, Monoidal p) => Monoidal (Cayley f p) where
--   oneP = Cayley (pure oneP)
--   Cayley x >*< Cayley y = Cayley ((>*<) <$> x <*> y)
-- instance (Functor f, Applicative g, Monoidal p)
--   => Monoidal (Biff p f g) where
--     oneP = Biff (dimap (const ()) pure oneP)
--     Biff x >*< Biff y = Biff $ dimap
--       ((fst <$>) &&& (snd <$>))
--       (uncurry (liftA2 (,)))
--       (x >*< y)
instance Monoidal p => Applicative (Yoneda p x) where
  pure = proreturn . pure
  ab <*> cd = proreturn (proextract ab <*> proextract cd)
instance Monoidal p => Applicative (Coyoneda p x) where
  pure = proreturn . pure
  ab <*> cd = proreturn (proextract ab <*> proextract cd)
