{-|
Module      : Data.Profunctor.Distributor
Description : distributors
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Data.Profunctor.Distributor
  ( -- * Distributor
    Distributor (..)
    -- * Alternator
  , Alternator (..)
    -- * SepBy
  , SepBy (..)
  , sepBy
  , noSep
    -- * SepBy Combinators
  , several
  , several1
  , chain
  , chain1
  , intercalateP
    -- * Operator Expressions
  , Operator (..)
  , Assoc (..)
  , withOperators
  ) where

import Control.Applicative hiding (WrappedArrow)
import Control.Applicative qualified as Ap (WrappedArrow)
import Control.Arrow
import Control.Lens hiding (chosen)
import Control.Lens.Internal.Profunctor
import Control.Lens.PartialIso
import Data.Bifunctor.Clown
import Data.Bifunctor.Joker
import Data.Bifunctor.Product
import Data.Functor.Adjunction
import Data.Functor.Contravariant.Divisible
import Data.Monoid.Disjunctive
import Data.Profunctor hiding (WrappedArrow)
import Data.Profunctor qualified as Pro (WrappedArrow)
import Data.Profunctor.Cayley
import Data.Profunctor.Composition
import Data.Profunctor.Monad
import Data.Profunctor.Monoidal
import Data.Profunctor.Yoneda
import Data.Profunctor.Monoidal.Cocartesian
import GHC.Exts (IsList (..))

-- Distributor --

{- | A `Distributor`, or lax distributive profunctor,
respects [distributive category]
(https://ncatlab.org/nlab/show/distributive+category)
structure, that is nilary and binary products and coproducts,
@()@, @(,)@, `Data.Void.Void` and `Either`, being both
`Monoidal` and `CocartesianMonoidal`.

`Distributor` additionally has methods `manyP` & `optionalP`,
distributing an action over @[]@ and `Maybe` datatypes,
which generalize to `Data.Traversable.Homogeneous.homogeneously`
distributing an action over
`Data.Traversable.Homogeneous.Homogeneous`
sum-of-products datatypes.
-}
class (Monoidal p, CocartesianMonoidal p) => Distributor p where

  {- | One or none. -}
  optionalP :: p a b -> p (Maybe a) (Maybe b)
  optionalP p = eotMaybe . swapped >~ p >+< oneP

  {- | Zero or more. -}
  manyP :: p a b -> p [a] [b]
  manyP p = eotList . swapped >~ p >*< manyP p >+< oneP

instance Distributor (->)
instance Monoid s => Distributor (Forget s)
instance Decidable f => Distributor (Clown f)
instance Alternative f => Distributor (Joker f) where
  optionalP (Joker x) = Joker (optional x)
  manyP (Joker x) = Joker (many x)
instance (Distributor p, Applicative f)
  => Distributor (WrappedPafb f p) where
    manyP (WrapPafb x) = WrapPafb (rmap sequenceA (manyP x))
    optionalP (WrapPafb x) = WrapPafb (rmap sequenceA (optionalP x))
instance Applicative f => Distributor (Star f) where
  optionalP (Star f) = Star (traverse f)
  manyP (Star f) = Star (traverse f)
deriving via (Star m) instance Monad m => Distributor (Kleisli m)
instance Adjunction f u => Distributor (Costar f)
instance (Applicative f, Distributor p)
  => Distributor (Cayley f p) where
    optionalP (Cayley x) = Cayley (optionalP <$> x)
    manyP (Cayley x) = Cayley (manyP <$> x)
instance (ArrowZero p, ArrowChoice p)
  => Distributor (Pro.WrappedArrow p)
deriving via (Pro.WrappedArrow p)
  instance (ArrowZero p, ArrowChoice p)
    => Distributor (Ap.WrappedArrow p)
instance (Distributor p, Distributor q)
  => Distributor (Procompose p q) where
    optionalP (Procompose f g) =
      Procompose (optionalP f) (optionalP g)
    manyP (Procompose f g) =
      Procompose (manyP f) (manyP g)
instance (Distributor p, Distributor q)
  => Distributor (Product p q) where
    optionalP (Pair f g) =
      Pair (optionalP f) (optionalP g)
    manyP (Pair f g) =
      Pair (manyP f) (manyP g)
instance Distributor p => Distributor (Yoneda p) where
  optionalP = proreturn . optionalP . proextract
  manyP = proreturn . manyP . proextract
instance Distributor p => Distributor (Coyoneda p) where
  optionalP = proreturn . optionalP . proextract
  manyP = proreturn . manyP . proextract

-- Alternator --

{- | The `Alternator` class co-extends `CocartesianChoice` and `Distributor`,
as well as `Alternative`, adding methods `someP` & `optionP`,
with these laws relating them.

> prop> manyP p = optionP _Empty (someP p)
> prop> optionalP p = optionP _Nothing (_Just >? p)
> prop> someP p = p >:< manyP p

These mirror the laws of a `KleeneStarAlgebra`, @starK x = optK (plusK x)@
& @plusK x = x <> starK x@, unfolding `someP` on the left.
Its unfolding on the right, @someP p = snocP (manyP p) p@,
mirroring @plusK x = starK x <> x@, isn't a law though,
since a greedy or predictive parser's `manyP` consumes every @p@,
leaving none for the last; only a backtracking one finds it.

Its `Alternative` structure agrees with its `Alternator` structure,
`many` & `some` repeating an input for `manyP` & `someP`.

> prop> empty = falseP
> prop> (<|>) = (>|<)
> prop> many = lmap repeat . manyP
> prop> some = lmap repeat . someP

Not all `Distributor`s are `Alternator`s, in particular @(->)@ is
a `Distributor` but cannot be `Alternative`,
because there is no general polymorphic function @empty :: a -> b@,
so @(->)@ isn't an `Alternator`.

-}
class (Distributor p, CocartesianChoice p, forall x. Alternative (p x))
  => Alternator p where

    {- | One or more. -}
    someP :: p a b -> p [a] [b]
    someP x = x >:< manyP x

    {- | One or zero-with-default. -}
    optionP :: APrism a b () () {- ^ default -} -> p a b -> p a b
    optionP def p = p >|< pureP def

instance (Alternator p, Applicative f)
  => Alternator (WrappedPafb f p) where
    someP (WrapPafb x) = WrapPafb (rmap sequenceA (someP x))
    optionP def (WrapPafb x) = WrapPafb (optionP (prism pure pure . def) x)
instance Alternator p => Alternator (Coyoneda p) where
  someP = proreturn . someP . proextract
  optionP def = proreturn . optionP def . proextract
instance Alternator p => Alternator (Yoneda p) where
  someP = proreturn . someP . proextract
  optionP def = proreturn . optionP def . proextract
instance Alternative f => Alternator (Joker f) where
  someP (Joker x) = Joker (some x)
  optionP def (Joker x) =
    Joker (x <|> withPrism def (\f _ -> pure (f ())))

-- Separators --

{- | Used to sequence multiple times,
separated by a `separateBy`,
begun by a `beginBy`,
and ended by an `endBy`. -}
data SepBy p = SepBy
  { beginBy :: p
  , endBy :: p
  , separateBy :: p
  } deriving stock
    ( Functor, Foldable, Traversable
    , Eq, Ord, Show, Read
    )

{- | A t'SepBy' smart constructor,
setting the `separateBy` field.
Beginning and ending delimiters will be no-ops,
except by modifier record updates `beginBy` or `endBy`. -}
sepBy :: Applicative p => p () -> SepBy (p ())
sepBy = SepBy (pure ()) (pure ())

{- | A t'SepBy' smart constructor for no separator,
beginning or ending delimiters. -}
noSep :: Applicative p => SepBy (p ())
noSep = sepBy (pure ())

{- |
> prop> several noSep = manyP
-}
several
  :: (IsList s, IsList t, Distributor p)
  => SepBy (p () ()) -> p (Item s) (Item t) -> p s t
several (SepBy beg end sep) p = iso toList fromList . eotList . swapped >~
  beg >* (p >*< manyP (sep >* p) >+< oneP) *< end

{- |
> prop> several1 noSep = someP
-}
several1
  :: (IsList s, IsList t, Distributor p, Choice p)
  => SepBy (p () ()) -> p (Item s) (Item t) -> p s t
several1 (SepBy beg end sep) p = iso toList fromList . _Cons >?
  beg >* (p >*< manyP (sep >* p)) *< end

{- | Use a nilary constructor pattern to sequence zero times, or
associate a binary constructor pattern to sequence one or more times. -}
chain
  :: Alternator p
  => (forall x. x -> Either x x) -- ^ `Left` or `Right` associate
  -> APartialIso a b (a,a) (b,b) -- ^ binary constructor pattern
  -> APrism a b () () -- ^ nilary constructor pattern
  -> SepBy (p () ()) -> p a b -> p a b
chain association pat2 pat0 (SepBy beg end sep) p =
  beg >* optionP pat0 (chain1 association pat2 (sepBy sep) p) *< end

{- | Associate a binary constructor pattern to sequence one or more times. -}
chain1
  :: (Distributor p, Choice p)
  => (forall x. x -> Either x x) -- ^ `Left` or `Right` associate
  -> APartialIso a b (a,a) (b,b) -- ^ binary constructor pattern
  -> SepBy (p () ()) -> p a b -> p a b
chain1 association pat (SepBy beg end sep) = leftOrRight chainl1 chainr1
  where
    leftOrRight a b = case association () of Left _ -> a; Right _ -> b
    chainl1 p = difoldl pat >? beg >* p >*< manyP (sep >* p) *< end
    chainr1 p = difoldr pat >? beg >* manyP (p *< sep) >*< p *< end

{- | Add a t'SepBy' to `replicateP` using `intercalateP`. -}
intercalateP
  :: (Monoidal p, Choice p, AsEmpty s, Cons s s a a)
  => Int {- ^ number of repetitions -}
  -> SepBy (p () ()) -> p a a -> p s s
intercalateP n (SepBy beg end _) _ | n <= 0 =
  beg >* asEmpty *< end
intercalateP n (SepBy beg end comma) p =
  beg >* p >:< replicateP (n-1) (comma >* p) *< end

{- | An operator at some level of an operator table, for use with
`withOperators`. `Infix` takes an `Assoc` to distinguish binary operators;
`Prefix` & `Postfix` are for unary operators. -}
data Operator p a b where
  Infix
    :: Assoc -- ^ `NonAssoc`, `LeftAssoc`, `RightAssoc`
    -> APrism a b (a,a) (b,b) -- ^ binary constructor pattern
    -> p () () -- ^ operator symbol
    -> Operator p a b
  Prefix
    :: APrism a b a b -- ^ unary constructor pattern
    -> p () () -- ^ operator symbol
    -> Operator p a b
  Postfix
    :: APrism a b a b -- ^ unary constructor pattern
    -> p () () -- ^ operator symbol
    -> Operator p a b

{- | The associativity of an `Infix` binary operator. -}
data Assoc = NonAssoc | LeftAssoc | RightAssoc
  deriving stock (Eq, Ord, Show, Read)

{- | Build an expression `Alternator` from a table of `Operator`s and
an atomic term `Alternator`, analogous to @buildExpressionParser@ from
[parsec](https://hackage.haskell.org/package/parsec).

The operator table is a list of list of operators, ordered from highest to lowest precedence.
Each level is a list of `Operator`s which share precedence.
Within a level, `Infix` takes an `Assoc` to set left, right or non-associativity for binary operators,
while `Prefix` & `Postfix` are for unary operators.

For an example, see the expression grammar in "Control.Lens.Grammar",
of natural numbers with postfix, right-associative & left-associative operators.
-}
withOperators
  :: Alternator p
  => [[Operator p a b]] -- ^ operator table
  -> p a b -- ^ atomic term
  -> p a b -- ^ expression
withOperators table p = foldl makeLevel p table
  where
    makeLevel term ops =
      let
        (infixes, pres, posts) = foldr splitOp ([],[],[]) ops
        termP = withPostP posts (withPreP pres term)
      in
        infixP infixes termP

    splitOp oper (infixes, pres, posts) = case oper of
      Infix associativity pat sym -> ((associativity,pat,sym):infixes, pres, posts)
      Prefix pat sym -> (infixes, (pat,sym):pres, posts)
      Postfix pat sym -> (infixes, pres, (pat,sym):posts)

    tagSepP syms = orP [only i >? sym | (i, sym) <- zip [0 :: Int ..] syms]

    withPreP ops inner =
      difoldr (taggedP (,) id (fst <$> ops))
        >? manyP (tagSepP (snd <$> ops)) >*< inner

    withPostP ops inner =
      difoldl (taggedP (flip (,)) (\(y,i) -> (i,y)) (fst <$> ops))
        >? inner >*< manyP (tagSepP (snd <$> ops))

    -- unary operators' patterns, tagged by their positions,
    -- & tried in turn, as one partial isomorphism
    taggedP
      :: (Int -> x -> c) -- ^ tag a match
      -> (d -> (Int, y)) -- ^ untag a build
      -> [APrism x y x y] -> PartialIso x y c d
    taggedP tag untag pats =
      let (fwd, bwd) = orP (zipWith exchange [0 ..] pats) in partialIso fwd bwd
      where
        exchange i pat = let (match, build) = patternFns pat in
          (fmap (tag i) . match, \d -> case untag d of
            (j, y) | j == i -> Just (build y)
            _ -> Nothing)

    -- An operand, then @(operator, operand)@ steps, folded by each
    -- operator's associativity, like parsec's @buildExpressionParser@:
    -- https://hackage.haskell.org/package/parsec/docs/src/Text.Parsec.Expr.html
    infixP infixes term =
      prism (uncurry go) (Right . fwd) >? term >*< manyP (tagSepP syms >*< term)
      where
        syms = [sym | (_,_,sym) <- infixes]
        fns = [(associativity,f,g) | (associativity,pat,_) <- infixes, let (f,g) = patternFns pat]

        assocOf i = let (associativity,_,_) = fns !! i in associativity
        applyTag i (l,r) = let (_,_,g) = fns !! i in g (l,r)

        -- fold a shared seed together with a left-to-right list of tagged
        -- steps, dispatching on each step's `Assoc`iativity in turn
        go l [] = l
        go l ((i,r):more) = case assocOf i of
          RightAssoc -> applyTag i (l, go r more)
          _          -> go (applyTag i (l,r)) more

        -- the exact inverse of `go`: decompose a value into a seed and the
        -- list of tagged steps that `go` would fold back into that value
        fwd x = decompose x
          where
            decompose y = case tryTags y of
              Nothing -> (y, [])
              Just (i,l,r) -> case assocOf i of
                RightAssoc ->
                  let (r0, rest) = decompose r in (l, (i,r0) : rest)
                _ ->
                  let (l0, prior) = decompose l in (l0, prior ++ [(i,r)])
            tryTags y = orP
              [ (\(l,r) -> (i,l,r)) <$> f y
              | (i,(_,f,_)) <- zip [0 :: Int ..] fns ]

    -- an operator's constructor pattern, matching partially & building totally
    patternFns pat = withPrism pat $ \construct match ->
      (either (const Nothing) Just . match, construct)
