-- `Varifocal` requires a `Filterable` monad, so that every
-- `Control.Lens.Bifocal.Bifocal` is a `Varifocal`, which the stepping
-- combinators, generic in their streams, needn't use.
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{- |
Module      : Control.Lens.Varifocal
Description : varifocals
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Control.Lens.Varifocal
  ( -- * Varifocal
    Varifocal
  , Varifocal'
  , AVarifocal
  , Varifocus (..)
  , varifocus
  , runVarifocus
  , runVarifocusT
  , cloneVarifocal
  , crossVarifocal
  , altVarifocal
  , orVarifocal
  , bindVarifocal
    -- * Applicator
  , contextually
  , contextuallyT
    -- * Combinators
  , stepping
  , steppingTree
  , terminateBy
  , delimitBy
  , balanceBy
  , countWith
  , arityWith
  ) where

import Control.Applicative (Alternative (..))
import Control.Comonad.Cofree (Cofree (..))
import Control.Lens hiding ((:<))
import Control.Lens.PartialIso ((>?), (>~))
import Control.Monad (MonadPlus (..), ap)
import Data.Bool (bool)
import Data.Foldable (toList)
import Data.Functor (void)
import Data.Traversable (mapAccumL)
import Data.Monoid.Disjunctive (DisjunctiveMonoid (..), anyP)
import Data.Profunctor (Cochoice (..))
import Data.Profunctor.Distributor
import Data.Profunctor.Filtrator (Filtrator (..), mfiltrate)
import Data.Profunctor.Monadic (Monadic, MonadicTrans (..))
import qualified Data.Profunctor.Monadic.Do as P
import Data.Profunctor.Monoidal (asEmpty, (>*<))
import Data.Profunctor.Monoidal.Cocartesian
import Witherable (Filterable (..))

{- | `Varifocal`s are context-sensitive bidirectional parser optics,
whose shape may depend on the foci they build,
as varifocal lenses refocus by what they're looking at.
Their `Applicative` is the monad @m@ of a `MonadicTrans` profunctor,
whose effects it absorbs by `joinP`, so failure & choice backwards
have a home, rather than needing flattening.

`Control.Lens.Bifocal.Bifocal` ⊂ `Varifocal`,

instantiating a `Control.Lens.Bifocal.Bifocal`'s @p@ & @f@
as @p m@ & @m@, so every `Control.Lens.Prism.Prism`,
`Control.Lens.Prismoid.Prismoid` & `Control.Lens.Bifocal.Bifocal`
is a `Varifocal` too, composing with them by @(.)@.

Unlike them, a `Varifocal` needs a `MonadicTrans` profunctor,
like a @Data.Profunctor.Grammar.Printor@ or @Parsor@,
so static ones, like a @Data.Profunctor.Grammar.Grammor@, can't run it.
Nor can a @Data.Profunctor.Grammar.Parsector.Parsector@, by design:
its failure backtracks by its state, which a `Varifocal`'s failure,
by its monad's `mzero`, can't reach, & its backtracking can't undo
a monad's effects.
-}
type Varifocal s t a b = forall p m.
  (MonadicTrans p, Alternator (p m), MonadPlus m, Filterable m)
    => p m a (m b) -> p m s (m t)

{- | A simple `Varifocal`. -}
type Varifocal' s a = Varifocal s s a a

{- | `AVarifocal` is monomorphically a `Varifocal`,
at the free t'Varifocus', whose monad is the list monad,
which embeds into every `MonadPlus`.

> prop> Varifocal s t a b ⊂ AVarifocal s t a b
-}
type AVarifocal s t a b =
  Varifocus a b [] a [b] -> Varifocus a b [] s [t]

{- | A t'Varifocus' is the concrete form of a `Varifocal`,
a free `MonadicTrans` `Alternator` on one `FocusP`: its syntax,
with a constructor for each method which can't be derived,
& for each one which a target may override, like `manyP`,
so that running it, by `runVarifocus`, keeps the target's own.
Its `Filterable`, `Cochoice` & `Filtrator` derive from its
`Monad` & `Alternative`, by `mfiltrate`.
-}
data Varifocus a b m s t where
  FocusP :: Varifocus a b m a b
  LiftP :: m t -> Varifocus a b m s t
  BindP
    :: Varifocus a b m s x
    -> (x -> Varifocus a b m s t)
    -> Varifocus a b m s t
  LmapP :: (s -> s') -> Varifocus a b m s' t -> Varifocus a b m s t
  AltsP :: [Varifocus a b m s t] -> Varifocus a b m s t
  AlternateP
    :: Either (Varifocus a b m s t) (Varifocus a b m s' t')
    -> Varifocus a b m (Either s s') (Either t t')
  ManyP :: Varifocus a b m s t -> Varifocus a b m [s] [t]
  OptionalP :: Varifocus a b m s t -> Varifocus a b m (Maybe s) (Maybe t)
  SomeP :: Varifocus a b m s t -> Varifocus a b m [s] [t]
  OptionP :: APrism s t () () -> Varifocus a b m s t -> Varifocus a b m s t
  ManyTillP
    :: Varifocus a b m s t
    -> Varifocus a b m [s] [t]
    -> Varifocus a b m [s] [t]
instance Monad m => Profunctor (Varifocus a b m) where
  dimap f g = lmap f . rmap g
  lmap = LmapP
  rmap g x = BindP x (LiftP . pure . g)
instance Monad m => Functor (Varifocus a b m s) where fmap = rmap
instance Monad m => Applicative (Varifocus a b m s) where
  pure = LiftP . pure
  (<*>) = ap
instance Monad m => Monad (Varifocus a b m s) where
  (>>=) = BindP
instance Monad m => Alternative (Varifocus a b m s) where
  empty = AltsP []
  x <|> y = AltsP [x, y]
  many = lmap repeat . manyP
  some = lmap repeat . someP
instance Monad m => DisjunctiveMonoid (Varifocus a b m s t)
instance Monad m => Choice (Varifocus a b m) where
  left' = AlternateP . Left
  right' = AlternateP . Right
instance Monad m => CocartesianMonoidal (Varifocus a b m)
instance Monad m => CocartesianChoice (Varifocus a b m) where
  alternate = AlternateP
instance Monad m => Distributor (Varifocus a b m) where
  manyP = ManyP
  optionalP = OptionalP
instance Monad m => Alternator (Varifocus a b m) where
  someP = SomeP
  optionP = OptionP
  manyTillP = ManyTillP
instance Monad m => Filterable (Varifocus a b m s) where
  mapMaybe f x = x >>= maybe empty pure . f
instance Monad m => Cochoice (Varifocus a b m) where
  unleft = fst . filtrate
  unright = snd . filtrate
instance Monad m => Filtrator (Varifocus a b m) where
  filtrate = mfiltrate
instance MonadicTrans (Varifocus a b) where
  liftP = LiftP

{- | The t'Varifocus' of `AVarifocal`, at any `MonadPlus`,
into which its list monad's choices embed.
-}
varifocus :: MonadPlus m => AVarifocal s t a b -> Varifocus a b m s t
varifocus vari = go (joinP (vari (rmap pure FocusP)))
  where
    go :: MonadPlus m => Varifocus a b [] s' t' -> Varifocus a b m s' t'
    go = \case
      FocusP -> FocusP
      LiftP xs -> LiftP (foldr (mplus . pure) mzero xs)
      BindP x k -> BindP (go x) (go . k)
      LmapP f x -> LmapP f (go x)
      AltsP xs -> AltsP (map go xs)
      AlternateP e -> AlternateP (either (Left . go) (Right . go) e)
      ManyP x -> ManyP (go x)
      OptionalP x -> OptionalP (go x)
      SomeP x -> SomeP (go x)
      OptionP d x -> OptionP d (go x)
      ManyTillP x y -> ManyTillP (go x) (go y)

{- | Run a t'Varifocus' of the list monad on a `Monadic` `Alternator`,
interpreting each constructor by its method,
& its lists of choices by the `Alternator`'s own.
-}
runVarifocus
  :: forall p a b s t. (Monadic p, Alternator p)
  => Varifocus a b [] s t -> p a b -> p s t
runVarifocus v p = go v
  where
    go :: Varifocus a b [] s' t' -> p s' t'
    go = \case
      FocusP -> p
      LiftP xs -> anyP pure xs
      BindP x k -> go x >>= go . k
      LmapP f x -> lmap f (go x)
      AltsP xs -> anyP go xs
      AlternateP e -> alternate (either (Left . go) (Right . go) e)
      ManyP x -> manyP (go x)
      OptionalP x -> optionalP (go x)
      SomeP x -> someP (go x)
      OptionP d x -> optionP d (go x)
      ManyTillP x y -> manyTillP (go x) (go y)

{- | Run a t'Varifocus' on a `MonadicTrans` `Alternator`,
interpreting each constructor by its method.
-}
runVarifocusT
  :: forall p m a b s t. (MonadicTrans p, Alternator (p m), Monad m)
  => Varifocus a b m s t -> p m a b -> p m s t
runVarifocusT v p = go v
  where
    go :: Varifocus a b m s' t' -> p m s' t'
    go = \case
      FocusP -> p
      LiftP mt -> liftP mt
      BindP x k -> go x >>= go . k
      LmapP f x -> lmap f (go x)
      AltsP xs -> anyP go xs
      AlternateP e -> alternate (either (Left . go) (Right . go) e)
      ManyP x -> manyP (go x)
      OptionalP x -> optionalP (go x)
      SomeP x -> someP (go x)
      OptionP d x -> optionP d (go x)
      ManyTillP x y -> manyTillP (go x) (go y)

{- | Clone `AVarifocal` so that you can reuse the same
monomorphically typed `Varifocal` for different purposes.
-}
cloneVarifocal :: AVarifocal s t a b -> Varifocal s t a b
cloneVarifocal vari q = rmap pure (runVarifocusT (varifocus vari) (joinP q))

{- | Two `AVarifocal`s of the same foci, side by side, on a pair. -}
crossVarifocal
  :: AVarifocal s t a b
  -> AVarifocal u v a b
  -> Varifocal (s,u) (t,v) a b
crossVarifocal x y q = rmap (uncurry (liftA2 (,)))
  (cloneVarifocal x q >*< cloneVarifocal y q)

{- | Two `AVarifocal`s of the same foci, one or the other, on a sum. -}
altVarifocal
  :: AVarifocal s t a b
  -> AVarifocal u v a b
  -> Varifocal (Either s u) (Either t v) a b
altVarifocal x y q = rmap (either (fmap Left) (fmap Right))
  (cloneVarifocal x q >+< cloneVarifocal y q)

{- | Two `AVarifocal`s of the same source, disjoined by `>|<`.

> prop> orVarifocal x falseOptic = cloneVarifocal x
> prop> orVarifocal falseOptic y = cloneVarifocal y
-}
orVarifocal
  :: AVarifocal s t a b
  -> AVarifocal s t a b
  -> Varifocal s t a b
orVarifocal x y q = cloneVarifocal x q >|< cloneVarifocal y q

{- | An `AVarifocal`, then another, chosen by what the first built,
on a pair, as only `Varifocal`s can,
like a netstring's length, then that many foci.

> prop> bindVarifocal x (const y) = crossVarifocal x y
-}
bindVarifocal
  :: AVarifocal s t a b
  -> (t -> AVarifocal u v a b)
  -> Varifocal (s,u) (t,v) a b
bindVarifocal x k q = rmap pure
  (joinP (cloneVarifocal x q) P.>>= \t -> joinP (cloneVarifocal (k t) q))

{- | Action of `AVarifocal` on `Monadic` `Alternator`s,
like a @Control.Lens.Grammar.CtxGrammar@'s, by its t'Varifocus',
whose choices & failures are the `Alternator`'s own,
so that it backtracks as the `Alternator` does.

> prop> contextually vari = runVarifocus (varifocus vari)
-}
contextually
  :: (Monadic p, Alternator p)
  => AVarifocal s t a b -> p a b -> p s t
contextually vari = runVarifocus (varifocus vari)

{- | Action of a `Varifocal` on `MonadicTrans` `Alternator`s,
absorbing its monad by `joinP`, applying it directly.

> prop> contextuallyT vari p = joinP (vari (rmap pure p))
-}
contextuallyT
  :: (MonadicTrans p, Alternator (p m), MonadPlus m, Filterable m)
  => Varifocal s t a b -> p m a b -> p m s t
contextuallyT vari p = joinP (vari (rmap pure p))

{- | Foci stepped through by a deterministic machine, from a state,
deciding by each focus built whether to continue, @`Right` state@,
to stop there, @`Left` `True`@, or to reject, @`Left` `False`@,
as no `Control.Lens.Bifocal.Bifocal` can.
A stream, like a list, matches when its last focus,
& no earlier one, stops it.
-}
stepping
  :: (Cons s s a a, AsEmpty s)
  => st -> (st -> a -> Either Bool st) -> Varifocal' s a
stepping st0 step q = rmap pure (go st0)
  where
    go st = _Cons >? P.do
      b <- joinP q
      case step st b of
        Right st' -> go st'
        Left True -> asEmpty
        Left False -> empty

{- | Foci stepped through by a deterministic top-down tree machine,
from a state, deciding by each node's focus built which children
it has, a state for each position of a `Traversable` @g@,
or rejecting it, by `Nothing`, as no `Control.Lens.Bifocal.Bifocal` can.
Foci are visited in preorder, a node's before its children's.
A tree matches when each node's children have the shape
its focus decides, so that it parses as it prints.

`stepping` is `steppingTree` at `Maybe`, of non-empty streams,
as the cofree comonad of `Maybe`, by which
@`Left` `False`@, @`Left` `True`@ & @`Right` state@
decide `Nothing`, @`Just` `Nothing`@ & @`Just` (`Just` state)@;
`stepping` steps through a stream directly, rather than through
a `Cofree`, & needn't check a shape, as a stream's is its focus's.
-}
steppingTree
  :: (Traversable g, Eq (g ()))
  => st -> (st -> a -> Maybe (g st)) -> Varifocal' (Cofree g a) a
steppingTree st0 step q = rmap pure (go st0)
  where
    go st = cofreed >~ P.do
      b <- joinP q
      maybe empty offspring (step st b)
    offspring states = shaped states >? sequenceA
      (snd (mapAccumL (\i st -> (i + 1, child i st)) (0 :: Int) states))
    -- after shaping, the child at a position of the children
    child i st = lmap (\kids -> toList kids !! i) (go st)
    shaped states = prism' id $ \kids ->
      if void kids == void states then Just kids else Nothing
    cofreed = iso (\(b :< kids) -> (b, kids)) (uncurry (:<))

{- | Zero or more foci, then one which @end@s them, deciding by
each focus built, like a sentinel-terminated sequence, a C string's.
A stream which doesn't end by its first ending focus doesn't match.

> prop> terminateBy end = stepping () (\() -> bool (Right ()) (Left True) . end)
-}
terminateBy :: (Cons s s a a, AsEmpty s) => (a -> Bool) -> Varifocal' s a
terminateBy end = stepping () (\() -> bool (Right ()) (Left True) . end)

{- | Foci opened by the first, & closed by the first after it
which matches it, deciding by the opening focus built,
like a [heredoc](https://en.wikipedia.org/wiki/Here_document)'s tag,
or a fenced code block's fence, whose language,
of matching delimiters, isn't context-free.
A stream which doesn't close by its first match doesn't match.
-}
delimitBy :: (Cons s s a a, AsEmpty s) => (a -> a -> Bool) -> Varifocal' s a
delimitBy same = stepping Nothing $ \st b -> case st of
  Nothing -> Right (Just b)
  Just open -> bool (Right st) (Left True) (same open b)

{- | Foci opened by one which @open@s, & closed by the one which @close@s,
at the same nesting depth, like nested comments, @/* /* */ */@,
or a balanceBy block, whose language, of nested pairs, isn't regular.
A focus may not both @open@ & @close@.
A stream which doesn't open first, or close only last, doesn't match.
-}
balanceBy
  :: (Cons s s a a, AsEmpty s)
  => (a -> Bool) -> (a -> Bool) -> Varifocal' s a
balanceBy open close = stepping (0 :: Int) step
  where
    step depth b
      | open b = Right (depth + 1)
      | close b && depth == 1 = Left True
      | close b && depth > 1 = Right (depth - 1)
      | depth > 0 = Right depth
      | otherwise = Left False

{- | A focus counting how many foci follow it, then those,
like a length-prefixed record of bytes in a binary format.
A stream which doesn't have as many as its first focus counts
doesn't match.
-}
countWith :: (Cons s s a a, AsEmpty s) => (a -> Int) -> Varifocal' s a
countWith count = stepping Nothing $ \st b -> case st of
  Nothing -> if count b <= 0 then Left True else Right (Just (count b))
  Just n -> if n <= 1 then Left True else Right (Just (n - 1))

{- | A tree whose nodes' foci each count their children,
like a count-prefixed tree of records in a binary format,
by `steppingTree`, as `countWith` counts a stream's.
A node counting fewer than none doesn't match.
-}
arityWith :: (a -> Int) -> Varifocal' (Cofree [] a) a
arityWith arity = steppingTree () $ \() b ->
  if arity b < 0 then Nothing else Just (replicate (arity b) ())
