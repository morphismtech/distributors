{- |
Module      : Control.Lens.Monocle
Description : monocles
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable

See Oliveira, Jaskelioff & de Melo,
[On Structuring Functional Programs with Monoidal Profunctors](https://arxiv.org/abs/2207.00852)
-}

module Control.Lens.Monocle
  ( -- * Monocle
    Monocle
  , AMonocle
  , Monocular (..), runMonocular
  , Ditraversal (..), ditraversal, withDitraversal
    -- * Combinators
  , monocle
  , withMonocle
  , cloneMonocle
  , mapMonocle
  , crossMonocle
  , oneOptic
  , ditraversed
  , forevered
  , zipMonocle
  , zipWithMonocle
  , replicateMonocle
  , tabulateMonocle
  , fociMonocle
  ) where

import Control.Lens hiding (Traversing)
import Control.Lens.Internal.Profunctor
import Control.Monad.Trans.State.Lazy (evalState, state)
import Data.Distributive
import Data.Profunctor.Monoidal
import GHC.Generics (Par1 (..), U1 (..), (:*:) (..))
import Numeric.Natural (Natural)

-- $setup
-- >>> import Control.Lens
-- >>> import Data.Complex
-- >>> import Data.Foldable (toList)
-- >>> import Data.Functor.Identity

{- | `Monocle`s are an optic which is both
a `Control.Lens.Traversal.Traversal` & a `Control.Lens.Grate.Grate`,
focusing on a number of foci fixed by the optic, not its source.
`Control.Lens.Iso.Iso` ⊂ `Monocle` ⊂
`Control.Lens.Traversal.Traversal` ∩ `Control.Lens.Grate.Grate`.

`Monocle`s are isomorphic to t'Monocular's, & those of finitely many foci
to t'Ditraversal's, whose shapes are `Traversable` ∩ `Distributive`,
the shapes of `Control.Lens.Traversal.Traversal`s
∩ the shapes of `Control.Lens.Grate.Grate`s.
-}
type Monocle s t a b = forall p f.
  (Monoidal p, Applicative f)
    => p a (f b) -> p s (f t)

{- | `AMonocle` is monomorphically a `Monocle`.

> prop> Monocle s t a b ⊂ AMonocle s t a b
-}
type AMonocle s t a b =
  Monocular a b a (Identity b) -> Monocular a b s (Identity t)

{- | Build a `Monocle` from a concrete t'Monocular'. -}
monocle :: Monocular a b s t -> Monocle s t a b
monocle mon = unwrapPafb . runMonocular mon . WrapPafb

{- | Action of `AMonocle` on `Monoidal` `Profunctor`s. -}
mapMonocle :: Monoidal p => AMonocle s t a b -> p a b -> p s t
mapMonocle mon p = withMonocle mon $ \f -> lmap f p

{- | Clone `AMonocle` so that you can reuse the same
monomorphically typed `Monocle` for different purposes.
-}
cloneMonocle :: AMonocle s t a b -> Monocle s t a b
cloneMonocle mon = unwrapPafb . mapMonocle mon . WrapPafb

{- | The `Monocle` without foci, the unit of the crosses,
like `crossMonocle`, up to the unitor @(s,()) ≅ s@,
as `oneP` is of `>*<`, & by inclusion an optic of every
kind which crosses.

>>> toListOf oneOptic () :: [Int]
[]
-}
oneOptic :: Monocle () () a b
oneOptic _ = pure (pure ())

{- | Construct a `Monocle` on pairs from components, with the same foci,
since products of powers add, \(a^m \times a^n = a^{m+n}\),
as `Control.Lens.Traversal.beside` does `Control.Lens.Traversal.Traversal`s.

>>> over (crossMonocle id ditraversed) negate (1, 2 :+ 3)
(-1,(-2) :+ (-3))
-}
crossMonocle
  :: AMonocle s t a b
  -> AMonocle u v a b
  -> Monocle (s,u) (t,v) a b
crossMonocle x y p =
  rmap (uncurry (liftA2 (,))) (cloneMonocle x p >*< cloneMonocle y p)

{- | Build a `Monocle` from a `Traversable` & `Distributive`,
homogeneous, countable product.

> prop> traverse = ditraversed
> prop> cotraversed = ditraversed
-}
ditraversed :: (Traversable g, Distributive g) => Monocle (g a) (g b) a b
ditraversed = unwrapPafb . ditraverse . WrapPafb

{- | Repeat action indefinitely. -}
forevered :: Monocle s t () b
forevered = unwrapPafb . foreverP . WrapPafb

{- | Zip with `AMonocle`, by running it on the `Monoidal` `Profunctor`
of functions @f a -> g b@, generalizing both
`Control.Lens.Traversal.traverseOf`, at t'Identity' @f@,
& `Control.Lens.Grate.cotraverseOf`, at t'Identity' @g@.

>>> zipMonocle ditraversed (\xs -> [sum xs, product xs]) [1 :+ 2, 3 :+ 4 :: Complex Int]
[4 :+ 6,4 :+ 8,3 :+ 6,3 :+ 8]
-}
zipMonocle
  :: (Functor f, Applicative g)
  => AMonocle s t a b -> (f a -> g b) -> f s -> g t
zipMonocle mon f ss = withMonocle mon $ \get -> f (get <$> ss)

{- | Zip two sources with `AMonocle`; all of whose foci match.

>>> zipWithMonocle ditraversed (+) (1 :+ 2) (3 :+ 4 :: Complex Int)
4 :+ 6
-}
zipWithMonocle :: AMonocle s t a b -> (a -> a -> b) -> s -> s -> t
zipWithMonocle mon f s0 s1 =
  runIdentity (withMonocle mon (\get -> Identity (f (get s0) (get s1))))

{- | Sequence an action at every focus of `AMonocle`,
needing no source, by running it on the `Monoidal` `Profunctor`
@Joker g@, like `Control.Monad.replicateM`.

>>> replicateMonocle ditraversed "ab" :: [Complex Char]
['a' :+ 'a','a' :+ 'b','b' :+ 'a','b' :+ 'b']
-}
replicateMonocle :: Applicative g => AMonocle s t a b -> g b -> g t
replicateMonocle mon gb = withMonocle mon (const gb)

{- | Build from the index of each focus of `AMonocle`, numbered left to right,
like `Data.Functor.Rep.tabulate`.

>>> tabulateMonocle ditraversed fromIntegral :: Complex Int
0 :+ 1
-}
tabulateMonocle :: AMonocle s t a b -> (Natural -> b) -> t
tabulateMonocle mon f =
  evalState (replicateMonocle mon (state (\n -> (f n, n + 1)))) 0

{- | The `Control.Lens.Lens.Lens`es of the foci of `AMonocle`,
numbered from 0, left to right, every one of which focuses on a source.

Dual to `Control.Lens.Comonocle.copiesComonocle`: a product of foci has
a `Control.Lens.Lens.Lens` for each focus, every one of which focuses,
as a sum of copies has a `Control.Lens.Prism.Prism` for each copy,
exactly one of which matches.

>>> [view (runLens focus) (1 :+ 2) | focus <- fociMonocle ditraversed] :: [Int]
[1,2]
>>> [set (runLens focus) 0 (1 :+ 2) | focus <- fociMonocle ditraversed] :: [Complex Int]
[0 :+ 2,1 :+ 0]
-}
fociMonocle :: AMonocle s s a a -> [ReifiedLens' s a]
fociMonocle mon = zipWith focusAt [0 :: Natural ..] getters
  where
    getters = getConst (withMonocle mon (\get -> Const [get]))
    focusAt i get = Lens $ lens get $ \s a -> evalState
      (withMonocle mon (\get' -> state (\n -> (if n == i then a else get' s, n + 1))))
      0

{- | Run `AMonocle` over an `Applicative`. -}
withMonocle :: Applicative f => AMonocle s t a b -> ((s -> a) -> f b) -> f t
withMonocle mon = unMonocular (runIdentity <$> mon (Identity <$> Monocular ($ id)))

{- | t'Monocular' provides an efficient
concrete representation of `Monocle`s. -}
newtype Monocular a b s t = Monocular
  {unMonocular :: forall f. Applicative f => ((s -> a) -> f b) -> f t}
instance Profunctor (Monocular a b) where
  dimap f g (Monocular k) =
    Monocular (fmap g . k . (. (. f)))
instance Functor (Monocular a b s) where fmap = rmap
instance Applicative (Monocular a b s) where
  pure t = Monocular (pure (pure t))
  Monocular x <*> Monocular y = Monocular (liftA2 (<*>) x y)

{- | Run a t'Monocular' on a `Monoidal` `Profunctor`. -}
runMonocular :: Monoidal p => Monocular a b s t -> p a b -> p s t
runMonocular (Monocular k) p = k $ \f -> lmap f p

{- | t'Ditraversal' is a secondary concrete representation of `Monocle`s,
by homogeneous products: a `Traversable` & `Distributive` shape,
into which a source splits its foci, & from which a target merges them.

`Monocle`s with finitely many foci are isomorphic to t'Ditraversal's,
by `ditraversal` & `withDitraversal`.
-}
data Ditraversal a b s t where
  Ditraversal
    :: (Distributive f, Traversable f)
    => (s -> f a) -> (f b -> t) -> Ditraversal a b s t
instance Profunctor (Ditraversal a b) where
  dimap f g (Ditraversal split merge) = Ditraversal (split . f) (g . merge)
instance Functor (Ditraversal a b s) where fmap = rmap
{- | Shapes multiply by t':*:', with unit t'U1',
since products of powers add, \(a^m \times a^n = a^{m+n}\).
-}
instance Applicative (Ditraversal a b s) where
  pure t = Ditraversal (const U1) (const t)
  liftA2 h (Ditraversal split0 merge0) (Ditraversal split1 merge1) =
    Ditraversal
      (\s -> split0 s :*: split1 s)
      (\(b0 :*: b1) -> h (merge0 b0) (merge1 b1))
  (<*>) = liftA2 id

{- | Build a `Monocle` from a t'Ditraversal'.

>>> over (ditraversal (Ditraversal (uncurry (:+)) (\(x :+ y) -> (x, y)))) negate (1, 2)
(-1,-2)
-}
ditraversal :: Ditraversal a b s t -> Monocle s t a b
ditraversal (Ditraversal split merge) =
  dimap split (fmap merge) . ditraversed

{- | Convert `AMonocle` to the pair of functions that characterize it,
splitting into & merging from a homogeneous product of its foci.
It diverges for infinitely many foci, like those of `forevered`.

>>> withDitraversal (crossMonocle id ditraversed) $ \split _ -> toList (split (1, 2 :+ 3))
[1,2,3]
>>> withDitraversal ditraversed (\split merge -> merge (negate <$> split (1 :+ 2))) :: Complex Int
(-1) :+ (-2)
-}
withDitraversal
  :: AMonocle s t a b
  -> (forall f. (Distributive f, Traversable f)
      => (s -> f a) -> (f b -> t) -> r)
  -> r
withDitraversal mon k =
  case runMonocular monocular (Ditraversal Par1 unPar1) of
    Ditraversal split merge -> k split merge
  where
    monocular = runIdentity <$> mon (Identity <$> Monocular ($ id))
