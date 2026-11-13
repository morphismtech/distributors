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
    -- * Applicator
  , contextually
  , contextuallyT
    -- * Combinators
  , stepping
  , terminatedBy
  , delimited
  , balanced
  , countPrefixed
  ) where

import Control.Applicative (Alternative (..))
import Control.Lens
import Control.Lens.PartialIso ((>?))
import Control.Monad (MonadPlus (..), ap)
import Data.Monoid.Disjunctive (DisjunctiveMonoid)
import Data.Profunctor (Cochoice (..))
import Data.Profunctor.Distributor
import Data.Profunctor.Filtrator (Filtrator (..), mfiltrate)
import Data.Profunctor.Monadic (Monadic, MonadicTrans (..))
import qualified Data.Profunctor.Monadic.Do as P
import Data.Profunctor.Monoidal (asEmpty)
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
      LiftP xs -> case map pure xs of
        [] -> empty
        ys -> foldr1 (<|>) ys
      BindP x k -> go x >>= go . k
      LmapP f x -> lmap f (go x)
      AltsP xs -> case map go xs of
        [] -> empty
        ys -> foldr1 (<|>) ys
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
      AltsP xs -> case map go xs of
        [] -> empty
        ys -> foldr1 (<|>) ys
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
A list matches when its last focus, & no earlier one, stops it.
-}
stepping :: st -> (st -> a -> Either Bool st) -> Varifocal' [a] a
stepping st0 step q = rmap pure (go st0)
  where
    focus = joinP q
    go st = _Cons >? (focus P.>>= \b -> case step st b of
      Right st' -> go st'
      Left True -> asEmpty
      Left False -> empty)

{- | Zero or more foci, then one which @end@s them, deciding by
each focus built, like a sentinel-terminated sequence, a C string's.
A list which doesn't end by its first ending focus doesn't match.

> prop> terminatedBy end = stepping () (\() b -> if end b then Left True else Right ())
-}
terminatedBy :: (a -> Bool) -> Varifocal' [a] a
terminatedBy end = stepping () (\() b -> if end b then Left True else Right ())

{- | Foci opened by the first, & closed by the first after it
which matches it, deciding by the opening focus built,
like a [heredoc](https://en.wikipedia.org/wiki/Here_document)'s tag,
or a fenced code block's fence, whose language,
of matching delimiters, isn't context-free.
A list which doesn't close by its first match doesn't match.
-}
delimited :: (a -> a -> Bool) -> Varifocal' [a] a
delimited same = stepping Nothing $ \st b -> case st of
  Nothing -> Right (Just b)
  Just open -> if same open b then Left True else Right st

{- | Foci opened by one which @open@s, & closed by the one which @close@s,
at the same nesting depth, like nested comments, @/* /* */ */@,
or a balanced block, whose language, of nested pairs, isn't regular.
A focus may not both @open@ & @close@.
A list which doesn't open first, or close only last, doesn't match.
-}
balanced :: (a -> Bool) -> (a -> Bool) -> Varifocal' [a] a
balanced open close = stepping (0 :: Int) step
  where
    step depth b
      | open b = Right (depth + 1)
      | close b && depth == 1 = Left True
      | close b && depth > 1 = Right (depth - 1)
      | depth > 0 = Right depth
      | otherwise = Left False

{- | A focus counting how many foci follow it, then those,
like a length-prefixed record of bytes in a binary format.
A list which doesn't have as many as its first focus counts doesn't match.
-}
countPrefixed :: (a -> Int) -> Varifocal' [a] a
countPrefixed count = stepping Nothing $ \st b -> case st of
  Nothing -> if count b <= 0 then Left True else Right (Just (count b))
  Just n -> if n <= 1 then Left True else Right (Just (n - 1))
