{-# LANGUAGE DeriveAnyClass #-}
{- |
Module      : Data.Monoid.Disjunctive
Description : disjunctive monoids, Boolean & Kleene star algebras
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable

See Boole, [The Mathematical Analysis of Logic]
(https://www.gutenberg.org/files/36884/36884-pdf.pdf),
and Kleene, [Representation of Events in Nerve Nets and Finite Automata]
(https://www.rand.org/pubs/research_memoranda/RM704.html).
-}

module Data.Monoid.Disjunctive
  ( -- * DisjunctiveMonoid
    DisjunctiveMonoid (..)
  , orP, anyP
    -- * BooleanAlgebra
  , BooleanAlgebra (..)
  , andP, allP
    -- * KleeneStarAlgebra
  , KleeneStarAlgebra (..)
  ) where

import Control.Applicative
import Control.Arrow
import Control.Lens.Internal.Profunctor
import Control.Monad
import Data.Bifunctor.Joker
import Data.Bifunctor.Product qualified as Bifunctor
import Data.Functor.Compose
import Data.Functor.Contravariant
import Data.Functor.Identity
import Data.Functor.Product qualified as Functor
import Data.Monoid
import Data.Profunctor hiding (WrappedArrow (..))
import Data.Profunctor qualified as Pro (WrappedArrow (..))
import Data.Profunctor.Cayley
import Data.Profunctor.Monad
import Data.Profunctor.Yoneda
import Data.Proxy
import Control.Alternative.Free qualified as FreeAlt
import Control.Applicative.Backwards (Backwards)
import Control.Applicative.Lift (Lift)
import Control.Lens (ReifiedFold)
import Control.Monad.Free (Free)
import Control.Monad.Free.Church qualified as Church
import Control.Monad.Trans.Accum (AccumT)
import Control.Monad.Trans.Except (ExceptT)
import Control.Monad.Trans.Free (FreeT)
import Control.Monad.Trans.Free.Church (FT)
import Control.Monad.Trans.Identity (IdentityT)
import Control.Monad.Trans.Maybe (MaybeT)
import Control.Monad.Trans.Reader (ReaderT)
import Control.Monad.Trans.RWS.CPS qualified as CPSRWS
import Control.Monad.Trans.RWS.Lazy qualified as LazyRWS
import Control.Monad.Trans.RWS.Strict qualified as StrictRWS
import Control.Monad.Trans.Select (SelectT)
import Control.Monad.Trans.State.Lazy qualified as Lazy
import Control.Monad.Trans.State.Strict qualified as Strict
import Control.Monad.Trans.Writer.CPS qualified as CPSW
import Control.Monad.Trans.Writer.Lazy qualified as LazyW
import Control.Monad.Trans.Writer.Strict qualified as StrictW
import Data.Functor.Reverse (Reverse)
import Data.Bits (Bits (..))
import Data.Int (Int8, Int16, Int32, Int64)
import Data.IntMap (IntMap)
import Data.IntSet (IntSet)
import Data.Map (Map)
import Data.Sequence (Seq)
import Data.Set (Set)
import Data.Vector (Vector)
import Data.Word (Word8, Word16, Word32, Word64)
import Foreign.C.Types
import Foreign.Ptr (IntPtr, WordPtr)
import GHC.Conc (STM)
import Numeric.Natural (Natural)
import GHC.Generics
import Text.ParserCombinators.ReadP (ReadP)
import Text.ParserCombinators.ReadPrec (ReadPrec)
import Witherable (WrappedFoldable)

{- | A `DisjunctiveMonoid` is simply a monoid,
the only difference from `Monoid` being its semantics
are disjunctive logical "or" constructs.

It has a disjunction `>|<` with identity `falseP`,
like `Alternative`'s `<|>` & `empty`.

> prop> falseP >|< x = x = x >|< falseP
> prop> (x >|< y) >|< z = x >|< (y >|< z)
-}
class DisjunctiveMonoid a where

  -- | identity of disjunction
  falseP :: a
  default falseP :: (a ~ f x, Alternative f) => a
  falseP = empty

  -- | disjunction
  (>|<) :: a -> a -> a
  default (>|<) :: (a ~ f x, Alternative f) => a -> a -> a
  (>|<) = (<|>)
  infixl 3 >|<

-- | cumulative disjunction
orP :: (Foldable f, DisjunctiveMonoid a) => f a -> a
orP = foldl' (>|<) falseP

-- | existential
anyP :: (Foldable f, DisjunctiveMonoid b) => (a -> b) -> f a -> b
anyP f = foldl' (\b a -> b >|< f a) falseP

{- | A `BooleanAlgebra`, like `Bool`, supporting classical logical operations,
with disjunction `>|<` & false `falseP`.
-}
class DisjunctiveMonoid b => BooleanAlgebra b where

  -- | conjunction
  (>&<) :: b -> b -> b
  default (>&<)
    :: (b ~ f bool, BooleanAlgebra bool, Applicative f) => b -> b -> b
  (>&<) = liftA2 (>&<)

  -- | negation
  notP :: b -> b
  default notP
    :: (b ~ f bool, BooleanAlgebra bool, Functor f) => b -> b
  notP = fmap notP

  -- | true
  trueP :: b
  default trueP
    :: (b ~ f bool, BooleanAlgebra bool, Applicative f) => b
  trueP = pure trueP

-- | cumulative conjunction
andP :: (Foldable f, BooleanAlgebra b) => f b -> b
andP = foldl' (>&<) trueP

-- | universal
allP :: (Foldable f, BooleanAlgebra b) => (a -> b) -> f a -> b
allP f = foldl' (\b a -> b >&< f a) trueP

{- | A `KleeneStarAlgebra` is a semiring
with a generally non-commutative multiplication,
the `Monoid` concatenation operator `<>` with identity `mempty`;
and an idempotent `DisjunctiveMonoid` addition, the alternation operator `>|<`
with identity `falseP`.

> prop> x >|< x = x
> prop> falseP >|< x = x = x >|< falseP
> prop> falseP <> x = falseP = x <> falseP
> prop> mempty <> x = x = x <> mempty

It also has three unary Kleene quantifier operators;

* `optK`, zero or one,

> prop> optK x = mempty >|< x = x >|< mempty

* `plusK`, one or more,

> prop> plusK x = x <> starK x = starK x <> x

* and the eponymous `starK`, zero or more.

> prop> starK x = optK (plusK x)

-}
class (Monoid k, DisjunctiveMonoid k) => KleeneStarAlgebra k where
  starK, plusK, optK :: k -> k
  starK x = optK (plusK x)
  plusK x = x <> starK x
  optK x = mempty >|< x

--instances
instance DisjunctiveMonoid Bool where
  falseP = False
  (>|<) = (||)
instance BooleanAlgebra Bool where
  trueP = True
  notP = not
  (>&<) = (&&)
instance DisjunctiveMonoid Any where
  falseP = Any False
  Any x >|< Any y = Any (x || y)
instance BooleanAlgebra Any where
  trueP = Any True
  notP (Any x) = Any (not x)
  Any x >&< Any y = Any (x && y)
deriving via Generically () instance DisjunctiveMonoid ()
deriving via Generically () instance BooleanAlgebra ()
deriving via Generically () instance KleeneStarAlgebra ()
deriving via Generically (a, b)
  instance (DisjunctiveMonoid a, DisjunctiveMonoid b)
    => DisjunctiveMonoid (a, b)
deriving via Generically (a, b)
  instance (BooleanAlgebra a, BooleanAlgebra b) => BooleanAlgebra (a, b)
deriving via Generically (a, b)
  instance (KleeneStarAlgebra a, KleeneStarAlgebra b)
    => KleeneStarAlgebra (a, b)
deriving via Generically (a, b, c)
  instance (DisjunctiveMonoid a, DisjunctiveMonoid b, DisjunctiveMonoid c)
    => DisjunctiveMonoid (a, b, c)
deriving via Generically (a, b, c)
  instance (BooleanAlgebra a, BooleanAlgebra b, BooleanAlgebra c)
    => BooleanAlgebra (a, b, c)
deriving via Generically (a, b, c)
  instance (KleeneStarAlgebra a, KleeneStarAlgebra b, KleeneStarAlgebra c)
    => KleeneStarAlgebra (a, b, c)
deriving via Generically (a, b, c, d)
  instance
    ( DisjunctiveMonoid a, DisjunctiveMonoid b, DisjunctiveMonoid c
    , DisjunctiveMonoid d )
    => DisjunctiveMonoid (a, b, c, d)
deriving via Generically (a, b, c, d)
  instance
    ( BooleanAlgebra a, BooleanAlgebra b, BooleanAlgebra c
    , BooleanAlgebra d )
    => BooleanAlgebra (a, b, c, d)
deriving via Generically (a, b, c, d)
  instance
    ( KleeneStarAlgebra a, KleeneStarAlgebra b, KleeneStarAlgebra c
    , KleeneStarAlgebra d )
    => KleeneStarAlgebra (a, b, c, d)
deriving via Generically (a, b, c, d, e)
  instance
    ( DisjunctiveMonoid a, DisjunctiveMonoid b, DisjunctiveMonoid c
    , DisjunctiveMonoid d, DisjunctiveMonoid e )
    => DisjunctiveMonoid (a, b, c, d, e)
deriving via Generically (a, b, c, d, e)
  instance
    ( BooleanAlgebra a, BooleanAlgebra b, BooleanAlgebra c
    , BooleanAlgebra d, BooleanAlgebra e )
    => BooleanAlgebra (a, b, c, d, e)
deriving via Generically (a, b, c, d, e)
  instance
    ( KleeneStarAlgebra a, KleeneStarAlgebra b, KleeneStarAlgebra c
    , KleeneStarAlgebra d, KleeneStarAlgebra e )
    => KleeneStarAlgebra (a, b, c, d, e)
instance DisjunctiveMonoid b => DisjunctiveMonoid (x -> b) where
  falseP = const falseP
  f >|< g = \x -> f x >|< g x
instance BooleanAlgebra b => BooleanAlgebra (x -> b)
instance KleeneStarAlgebra k => KleeneStarAlgebra (x -> k) where
  starK = (starK .)
  plusK = (plusK .)
  optK = (optK .)
instance DisjunctiveMonoid (Predicate a) where
  falseP = Predicate falseP
  Predicate p >|< Predicate q = Predicate (p >|< q)
instance BooleanAlgebra (Predicate a) where
  trueP = Predicate trueP
  notP (Predicate p) = Predicate (notP p)
  Predicate p >&< Predicate q = Predicate (p >&< q)
deriving via Generically (Identity a)
  instance DisjunctiveMonoid a => DisjunctiveMonoid (Identity a)
deriving via Generically (Identity a)
  instance BooleanAlgebra a => BooleanAlgebra (Identity a)
deriving via Generically (Identity a)
  instance KleeneStarAlgebra a => KleeneStarAlgebra (Identity a)
deriving via Generically (Const a b)
  instance DisjunctiveMonoid a => DisjunctiveMonoid (Const a b)
deriving via Generically (Const a b)
  instance BooleanAlgebra a => BooleanAlgebra (Const a b)
deriving via Generically (Const a b)
  instance KleeneStarAlgebra a => KleeneStarAlgebra (Const a b)
deriving via Generically (Proxy a) instance DisjunctiveMonoid (Proxy a)
deriving via Generically (Proxy a) instance BooleanAlgebra (Proxy a)
deriving via Generically (Proxy a) instance KleeneStarAlgebra (Proxy a)
{- | Bits disjoin by `.|.`, & conjoin by `.&.`, of a Boolean algebra
of bit vectors, `Integer`'s of infinitely many bits, two's complement.
`Natural` has no `complement`, so it only disjoins.
-}
newtype Bitwise a = Bitwise a
instance Bits a => DisjunctiveMonoid (Bitwise a) where
  falseP = Bitwise zeroBits
  Bitwise x >|< Bitwise y = Bitwise (x .|. y)
instance Bits a => BooleanAlgebra (Bitwise a) where
  trueP = Bitwise (complement zeroBits)
  notP (Bitwise x) = Bitwise (complement x)
  Bitwise x >&< Bitwise y = Bitwise (x .&. y)
deriving via Bitwise Int instance DisjunctiveMonoid Int
deriving via Bitwise Int instance BooleanAlgebra Int
deriving via Bitwise Int8 instance DisjunctiveMonoid Int8
deriving via Bitwise Int8 instance BooleanAlgebra Int8
deriving via Bitwise Int16 instance DisjunctiveMonoid Int16
deriving via Bitwise Int16 instance BooleanAlgebra Int16
deriving via Bitwise Int32 instance DisjunctiveMonoid Int32
deriving via Bitwise Int32 instance BooleanAlgebra Int32
deriving via Bitwise Int64 instance DisjunctiveMonoid Int64
deriving via Bitwise Int64 instance BooleanAlgebra Int64
deriving via Bitwise Word instance DisjunctiveMonoid Word
deriving via Bitwise Word instance BooleanAlgebra Word
deriving via Bitwise Word8 instance DisjunctiveMonoid Word8
deriving via Bitwise Word8 instance BooleanAlgebra Word8
deriving via Bitwise Word16 instance DisjunctiveMonoid Word16
deriving via Bitwise Word16 instance BooleanAlgebra Word16
deriving via Bitwise Word32 instance DisjunctiveMonoid Word32
deriving via Bitwise Word32 instance BooleanAlgebra Word32
deriving via Bitwise Word64 instance DisjunctiveMonoid Word64
deriving via Bitwise Word64 instance BooleanAlgebra Word64
deriving via Bitwise Integer instance DisjunctiveMonoid Integer
deriving via Bitwise Integer instance BooleanAlgebra Integer
deriving via Bitwise IntPtr instance DisjunctiveMonoid IntPtr
deriving via Bitwise IntPtr instance BooleanAlgebra IntPtr
deriving via Bitwise WordPtr instance DisjunctiveMonoid WordPtr
deriving via Bitwise WordPtr instance BooleanAlgebra WordPtr
deriving via Bitwise CChar instance DisjunctiveMonoid CChar
deriving via Bitwise CChar instance BooleanAlgebra CChar
deriving via Bitwise CSChar instance DisjunctiveMonoid CSChar
deriving via Bitwise CSChar instance BooleanAlgebra CSChar
deriving via Bitwise CUChar instance DisjunctiveMonoid CUChar
deriving via Bitwise CUChar instance BooleanAlgebra CUChar
deriving via Bitwise CShort instance DisjunctiveMonoid CShort
deriving via Bitwise CShort instance BooleanAlgebra CShort
deriving via Bitwise CUShort instance DisjunctiveMonoid CUShort
deriving via Bitwise CUShort instance BooleanAlgebra CUShort
deriving via Bitwise CInt instance DisjunctiveMonoid CInt
deriving via Bitwise CInt instance BooleanAlgebra CInt
deriving via Bitwise CUInt instance DisjunctiveMonoid CUInt
deriving via Bitwise CUInt instance BooleanAlgebra CUInt
deriving via Bitwise CLong instance DisjunctiveMonoid CLong
deriving via Bitwise CLong instance BooleanAlgebra CLong
deriving via Bitwise CULong instance DisjunctiveMonoid CULong
deriving via Bitwise CULong instance BooleanAlgebra CULong
deriving via Bitwise CLLong instance DisjunctiveMonoid CLLong
deriving via Bitwise CLLong instance BooleanAlgebra CLLong
deriving via Bitwise CULLong instance DisjunctiveMonoid CULLong
deriving via Bitwise CULLong instance BooleanAlgebra CULLong
deriving via Bitwise CPtrdiff instance DisjunctiveMonoid CPtrdiff
deriving via Bitwise CPtrdiff instance BooleanAlgebra CPtrdiff
deriving via Bitwise CSize instance DisjunctiveMonoid CSize
deriving via Bitwise CSize instance BooleanAlgebra CSize
deriving via Bitwise CWchar instance DisjunctiveMonoid CWchar
deriving via Bitwise CWchar instance BooleanAlgebra CWchar
deriving via Bitwise CSigAtomic instance DisjunctiveMonoid CSigAtomic
deriving via Bitwise CSigAtomic instance BooleanAlgebra CSigAtomic
deriving via Bitwise CIntPtr instance DisjunctiveMonoid CIntPtr
deriving via Bitwise CIntPtr instance BooleanAlgebra CIntPtr
deriving via Bitwise CUIntPtr instance DisjunctiveMonoid CUIntPtr
deriving via Bitwise CUIntPtr instance BooleanAlgebra CUIntPtr
deriving via Bitwise CIntMax instance DisjunctiveMonoid CIntMax
deriving via Bitwise CIntMax instance BooleanAlgebra CIntMax
deriving via Bitwise CUIntMax instance DisjunctiveMonoid CUIntMax
deriving via Bitwise CUIntMax instance BooleanAlgebra CUIntMax
deriving via Bitwise CBool instance DisjunctiveMonoid CBool
deriving via Bitwise CBool instance BooleanAlgebra CBool
deriving via Bitwise Natural instance DisjunctiveMonoid Natural

{- | A `Predicate` is a Kleene algebra, as a Boolean algebra is,
of conjunction, `Predicate`'s `Monoid`, & disjunction,
whose star is true.

> prop> starK p = trueP
-}
instance KleeneStarAlgebra (Predicate a) where
  starK _ = trueP
  plusK = id
  optK _ = trueP

{- | An `Alternative` of `Monoid`s is a Kleene algebra of languages,
like a parser of words: its sequence is `Ap`'s `Monoid`, its
alternation `<|>`, & its star `many` concatenated. It's a near-semiring,
whose left distribution, @(x >|< y) <> z = (x <> z) >|< (y <> z)@,
a left-biased `Alternative` may not keep, & its star diverges where
`many` does, as of a non-empty list's.

> prop> starK (Ap x) = Ap (mconcat <$> many x)
> prop> plusK (Ap x) = Ap (mconcat <$> some x)
-}
instance (Alternative f, Monoid a, DisjunctiveMonoid (f a))
  => KleeneStarAlgebra (Ap f a) where
    starK (Ap x) = Ap (mconcat <$> many x)
    plusK (Ap x) = Ap (mconcat <$> some x)

-- | Sets & maps disjoin by their monoids, of union.
instance Ord a => DisjunctiveMonoid (Set a) where
  falseP = mempty
  (>|<) = (<>)
instance DisjunctiveMonoid IntSet where
  falseP = mempty
  (>|<) = (<>)
instance Ord k => DisjunctiveMonoid (Map k v) where
  falseP = mempty
  (>|<) = (<>)
instance DisjunctiveMonoid (IntMap v) where
  falseP = mempty
  (>|<) = (<>)
-- `Alternative`s disjoin by `empty` & `<|>`.
deriving anyclass instance DisjunctiveMonoid [a]
deriving anyclass instance DisjunctiveMonoid (Maybe a)
deriving anyclass instance DisjunctiveMonoid (IO a)
deriving anyclass instance DisjunctiveMonoid (STM a)
deriving anyclass instance DisjunctiveMonoid (ZipList a)
deriving anyclass instance DisjunctiveMonoid (ReadP a)
deriving anyclass instance DisjunctiveMonoid (ReadPrec a)
deriving anyclass instance DisjunctiveMonoid (U1 p)
deriving anyclass instance DisjunctiveMonoid (Seq a)
deriving anyclass instance DisjunctiveMonoid (Vector a)
deriving anyclass instance MonadPlus m => DisjunctiveMonoid (WrappedMonad m a)
deriving anyclass instance ArrowPlus a => DisjunctiveMonoid (WrappedArrow a b c)
deriving anyclass instance ArrowPlus a => DisjunctiveMonoid (ArrowMonad a b)
deriving anyclass instance Alternative f => DisjunctiveMonoid (Backwards f a)
deriving anyclass instance Alternative f => DisjunctiveMonoid (Lift f a)
deriving anyclass instance Alternative f => DisjunctiveMonoid (Reverse f a)
deriving anyclass instance Alternative m => DisjunctiveMonoid (IdentityT m a)
deriving anyclass instance Alternative m => DisjunctiveMonoid (ReaderT r m a)
deriving anyclass instance (Functor m, Monad m)
  => DisjunctiveMonoid (MaybeT m a)
deriving anyclass instance (Functor m, Monad m, Monoid e)
  => DisjunctiveMonoid (ExceptT e m a)
deriving anyclass instance (Functor m, MonadPlus m)
  => DisjunctiveMonoid (Lazy.StateT s m a)
deriving anyclass instance (Functor m, MonadPlus m)
  => DisjunctiveMonoid (Strict.StateT s m a)
deriving anyclass instance (Monoid w, Alternative m)
  => DisjunctiveMonoid (LazyW.WriterT w m a)
deriving anyclass instance (Monoid w, Alternative m)
  => DisjunctiveMonoid (StrictW.WriterT w m a)
deriving anyclass instance (Functor m, MonadPlus m)
  => DisjunctiveMonoid (CPSW.WriterT w m a)
deriving anyclass instance (Monoid w, Functor m, MonadPlus m)
  => DisjunctiveMonoid (LazyRWS.RWST r w s m a)
deriving anyclass instance (Monoid w, Functor m, MonadPlus m)
  => DisjunctiveMonoid (StrictRWS.RWST r w s m a)
deriving anyclass instance (Functor m, MonadPlus m)
  => DisjunctiveMonoid (CPSRWS.RWST r w s m a)
deriving anyclass instance (Monoid w, Functor m, MonadPlus m)
  => DisjunctiveMonoid (AccumT w m a)
deriving anyclass instance (Functor m, MonadPlus m)
  => DisjunctiveMonoid (SelectT r m a)
deriving anyclass instance Alternative v => DisjunctiveMonoid (Free v a)
deriving anyclass instance Alternative f => DisjunctiveMonoid (Church.F f a)
deriving anyclass instance (Functor f, MonadPlus m)
  => DisjunctiveMonoid (FreeT f m a)
deriving anyclass instance Alternative m => DisjunctiveMonoid (FT f m a)
deriving anyclass instance DisjunctiveMonoid (FreeAlt.Alt f a)
deriving anyclass instance DisjunctiveMonoid (ReifiedFold s a)
deriving anyclass instance Alternative f => DisjunctiveMonoid (WrappedFoldable f a)
instance DisjunctiveMonoid (f a) => DisjunctiveMonoid (Alt f a) where
  falseP = Alt falseP
  Alt x >|< Alt y = Alt (x >|< y)
instance DisjunctiveMonoid (f a) => DisjunctiveMonoid (Ap f a) where
  falseP = Ap falseP
  Ap x >|< Ap y = Ap (x >|< y)
instance DisjunctiveMonoid (f (g a)) => DisjunctiveMonoid (Compose f g a) where
  falseP = Compose falseP
  Compose x >|< Compose y = Compose (x >|< y)
instance (DisjunctiveMonoid (f a), DisjunctiveMonoid (g a))
  => DisjunctiveMonoid (Functor.Product f g a) where
    falseP = Functor.Pair falseP falseP
    Functor.Pair x0 y0 >|< Functor.Pair x1 y1 =
      Functor.Pair (x0 >|< x1) (y0 >|< y1)
instance (DisjunctiveMonoid (f p), DisjunctiveMonoid (g p))
  => DisjunctiveMonoid ((f :*: g) p) where
    falseP = falseP :*: falseP
    (x0 :*: y0) >|< (x1 :*: y1) = (x0 >|< x1) :*: (y0 >|< y1)
instance DisjunctiveMonoid (f (g p)) => DisjunctiveMonoid ((f :.: g) p) where
  falseP = Comp1 falseP
  Comp1 x >|< Comp1 y = Comp1 (x >|< y)
instance DisjunctiveMonoid (f p) => DisjunctiveMonoid (M1 i c f p) where
  falseP = M1 falseP
  M1 x >|< M1 y = M1 (x >|< y)
instance DisjunctiveMonoid (f p) => DisjunctiveMonoid (Rec1 f p) where
  falseP = Rec1 falseP
  Rec1 x >|< Rec1 y = Rec1 (x >|< y)
instance DisjunctiveMonoid c => DisjunctiveMonoid (K1 i c p) where
  falseP = K1 falseP
  K1 x >|< K1 y = K1 (x >|< y)
instance DisjunctiveMonoid p => DisjunctiveMonoid (Par1 p) where
  falseP = Par1 falseP
  Par1 x >|< Par1 y = Par1 (x >|< y)
instance BooleanAlgebra (U1 p) where
  trueP = U1
  notP _ = U1
  _ >&< _ = U1
instance (BooleanAlgebra (f p), BooleanAlgebra (g p))
  => BooleanAlgebra ((f :*: g) p) where
    trueP = trueP :*: trueP
    notP (x :*: y) = notP x :*: notP y
    (x0 :*: y0) >&< (x1 :*: y1) = (x0 >&< x1) :*: (y0 >&< y1)
instance BooleanAlgebra (f (g p)) => BooleanAlgebra ((f :.: g) p) where
  trueP = Comp1 trueP
  notP (Comp1 x) = Comp1 (notP x)
  Comp1 x >&< Comp1 y = Comp1 (x >&< y)
instance BooleanAlgebra (f p) => BooleanAlgebra (M1 i c f p) where
  trueP = M1 trueP
  notP (M1 x) = M1 (notP x)
  M1 x >&< M1 y = M1 (x >&< y)
instance BooleanAlgebra (f p) => BooleanAlgebra (Rec1 f p) where
  trueP = Rec1 trueP
  notP (Rec1 x) = Rec1 (notP x)
  Rec1 x >&< Rec1 y = Rec1 (x >&< y)
instance BooleanAlgebra c => BooleanAlgebra (K1 i c p) where
  trueP = K1 trueP
  notP (K1 x) = K1 (notP x)
  K1 x >&< K1 y = K1 (x >&< y)
instance BooleanAlgebra p => BooleanAlgebra (Par1 p) where
  trueP = Par1 trueP
  notP (Par1 x) = Par1 (notP x)
  Par1 x >&< Par1 y = Par1 (x >&< y)
instance KleeneStarAlgebra (U1 p) where
  starK _ = U1
instance (KleeneStarAlgebra (f p), KleeneStarAlgebra (g p))
  => KleeneStarAlgebra ((f :*: g) p) where
    starK (x :*: y) = starK x :*: starK y
    plusK (x :*: y) = plusK x :*: plusK y
    optK (x :*: y) = optK x :*: optK y
instance KleeneStarAlgebra (f (g p)) => KleeneStarAlgebra ((f :.: g) p) where
  starK (Comp1 x) = Comp1 (starK x)
  plusK (Comp1 x) = Comp1 (plusK x)
  optK (Comp1 x) = Comp1 (optK x)
instance KleeneStarAlgebra (f p) => KleeneStarAlgebra (M1 i c f p) where
  starK (M1 x) = M1 (starK x)
  plusK (M1 x) = M1 (plusK x)
  optK (M1 x) = M1 (optK x)
instance KleeneStarAlgebra (f p) => KleeneStarAlgebra (Rec1 f p) where
  starK (Rec1 x) = Rec1 (starK x)
  plusK (Rec1 x) = Rec1 (plusK x)
  optK (Rec1 x) = Rec1 (optK x)
instance KleeneStarAlgebra c => KleeneStarAlgebra (K1 i c p) where
  starK (K1 x) = K1 (starK x)
  plusK (K1 x) = K1 (plusK x)
  optK (K1 x) = K1 (optK x)
instance KleeneStarAlgebra p => KleeneStarAlgebra (Par1 p) where
  starK (Par1 x) = Par1 (starK x)
  plusK (Par1 x) = Par1 (plusK x)
  optK (Par1 x) = Par1 (optK x)
instance (Generic a, DisjunctiveMonoid (Rep a ()))
  => DisjunctiveMonoid (Generically a) where
    falseP = Generically (to (falseP :: Rep a ()))
    Generically x >|< Generically y =
      Generically (to (from x >|< from y :: Rep a ()))
instance (Generic a, BooleanAlgebra (Rep a ()))
  => BooleanAlgebra (Generically a) where
    trueP = Generically (to (trueP :: Rep a ()))
    notP (Generically x) = Generically (to (notP (from x :: Rep a ())))
    Generically x >&< Generically y =
      Generically (to (from x >&< from y :: Rep a ()))
instance (Generic a, Monoid (Rep a ()), KleeneStarAlgebra (Rep a ()))
  => KleeneStarAlgebra (Generically a) where
    starK (Generically x) = Generically (to (starK (from x :: Rep a ())))
    plusK (Generically x) = Generically (to (plusK (from x :: Rep a ())))
    optK (Generically x) = Generically (to (optK (from x :: Rep a ())))
instance (Generic1 f, DisjunctiveMonoid (Rep1 f a))
  => DisjunctiveMonoid (Generically1 f a) where
    falseP = Generically1 (to1 (falseP :: Rep1 f a))
    Generically1 x >|< Generically1 y =
      Generically1 (to1 (from1 x >|< from1 y :: Rep1 f a))
instance DisjunctiveMonoid (m b) => DisjunctiveMonoid (Kleisli m a b) where
  falseP = Kleisli falseP
  Kleisli f >|< Kleisli g = Kleisli (f >|< g)
instance DisjunctiveMonoid (f b) => DisjunctiveMonoid (Star f a b) where
  falseP = Star falseP
  Star f >|< Star g = Star (f >|< g)
instance DisjunctiveMonoid r => DisjunctiveMonoid (Forget r a b) where
  falseP = Forget falseP
  Forget f >|< Forget g = Forget (f >|< g)
instance ArrowPlus p => DisjunctiveMonoid (Pro.WrappedArrow p a b) where
  falseP = Pro.WrapArrow zeroArrow
  Pro.WrapArrow x >|< Pro.WrapArrow y = Pro.WrapArrow (x <+> y)
instance (Applicative f, DisjunctiveMonoid (p a b))
  => DisjunctiveMonoid (Cayley f p a b) where
    falseP = Cayley (pure falseP)
    Cayley x >|< Cayley y = Cayley (liftA2 (>|<) x y)
instance (DisjunctiveMonoid (p a b), DisjunctiveMonoid (q a b))
  => DisjunctiveMonoid (Bifunctor.Product p q a b) where
    falseP = Bifunctor.Pair falseP falseP
    Bifunctor.Pair x0 y0 >|< Bifunctor.Pair x1 y1 =
      Bifunctor.Pair (x0 >|< x1) (y0 >|< y1)
instance Alternative f => DisjunctiveMonoid (Joker f a b) where
  falseP = Joker empty
  Joker x >|< Joker y = Joker (x <|> y)
instance DisjunctiveMonoid (p a (f b))
  => DisjunctiveMonoid (WrappedPafb f p a b) where
  falseP = WrapPafb falseP
  WrapPafb x >|< WrapPafb y = WrapPafb (x >|< y)
instance (Profunctor p, DisjunctiveMonoid (p a b))
  => DisjunctiveMonoid (Yoneda p a b) where
    falseP = proreturn falseP
    x >|< y = proreturn (proextract x >|< proextract y)
instance (Profunctor p, DisjunctiveMonoid (p a b))
  => DisjunctiveMonoid (Coyoneda p a b) where
    falseP = proreturn falseP
    x >|< y = proreturn (proextract x >|< proextract y)
