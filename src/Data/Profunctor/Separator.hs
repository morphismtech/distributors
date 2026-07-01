{-|
Module      : Data.Profunctor.Separator
Description : separators
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Data.Profunctor.Separator
  ( -- * SepBy
    SepBy (..)
  , sepBy
  , noSep
  , sepWith
  , beginWith
  , endWith
    -- * SepBy Combinators
  , several
  , several1
  , chain
  , chain1
  , intercalateP
    -- * Expression grammars
  , Operator (..)
  , buildExpressionG
  ) where

import Control.Applicative ((<|>))
import Control.Lens
import Control.Lens.PartialIso
import Control.Lens.Grammar.Symbol
import Data.Foldable (asum)
import Data.Profunctor (Cochoice)
import Data.Profunctor.Distributor
import Data.Profunctor.Monoidal
import GHC.Exts

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

{- | A `SepBy` smart constructor,
setting the `separateBy` field.
Beginning and ending delimitors will be no-ops,
except by modifier record updates `beginBy` or `endBy`. -}
sepBy :: Applicative p => p () -> SepBy (p ())
sepBy = SepBy (pure ()) (pure ())

{- | A `SepBy` smart constructor for no separator,
beginning or ending delimiters. -}
noSep :: Applicative p => SepBy (p ())
noSep = sepBy (pure ())

{- | A `SepBy` smart constructor like `sepBy`,
with a `terminal` argument.
Beginning and ending delimitors will be no-ops,
except by applying smart modifiers `beginWith` or `endWith`. -}
sepWith
  :: (Applicative p, TerminalSymbol c (p ()))
  => [c] -> SepBy (p ())
sepWith = sepBy . terminal

{- | A `SepBy` smart modifier like `beginBy`,
with a `terminal` argument. -}
beginWith :: TerminalSymbol c p => [c] -> SepBy p -> SepBy p
beginWith str separator = separator {beginBy = terminal str}

{- | A `SepBy` smart modifier like `endBy`,
with a `terminal` argument. -}
endWith :: TerminalSymbol c p => [c] -> SepBy p -> SepBy p
endWith str separator = separator {endBy = terminal str}

{- |
prop> several noSep = manyP
-}
several
  :: (IsList s, IsList t, Distributor p)
  => SepBy (p () ()) -> p (Item s) (Item t) -> p s t
several (SepBy beg end sep) p = iso toList fromList . eotList >~
  beg >* (p >*< manyP (sep >* p) >+< oneP) *< end

{- |
prop> several1 noSep = someP
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

{- | Add a `SepBy` to `replicateP` using `intercalateP`. -}
intercalateP
  :: (Monoidal p, Choice p, AsEmpty s, Cons s s a a)
  => Int {- ^ number of repetitions -}
  -> SepBy (p () ()) -> p a a -> p s s
intercalateP n (SepBy beg end _) _ | n <= 0 =
  beg >* asEmpty *< end
intercalateP n (SepBy beg end comma) p =
  beg >* p >:< replicateP (n-1) (comma >* p) *< end

{- | A single operator occupying one precedence level of a `buildExpressionG`
table. It is the invertible analogue of an operator in Parsec's
@buildExpressionParser@: instead of a parser that returns a combining function
(which could not be inverted), each operator carries the *constructor pattern*
that builds/matches its node, together with the grammar of its symbol.

* `Infix` is non-associative, `InfixL` left-associative, `InfixR`
  right-associative; their pattern is the binary constructor
  @APartialIso a b (a,a) (b,b)@ (a `Control.Lens.Prism.Prism` such as @_Add@
  works directly).
* `Prefix` and `Postfix` are unary; their pattern is @APartialIso a b a b@.

The symbol grammar is a delimiter @p () ()@ — e.g. @terminal "+"@, or even
whitespace for juxtaposition-application.

The constructor patterns at a level must be *disjoint* (each matches only its
own node shape); printing chooses an operator by matching, so overlapping
patterns would make the inverse ambiguous.
-}
data Operator p a b where
  Infix
    :: APartialIso a b (a, a) (b, b) -> p () () -> Operator p a b
  InfixL
    :: APartialIso a b (a, a) (b, b) -> p () () -> Operator p a b
  InfixR
    :: APartialIso a b (a, a) (b, b) -> p () () -> Operator p a b
  Prefix
    :: APartialIso a b a b -> p () () -> Operator p a b
  Postfix
    :: APartialIso a b a b -> p () () -> Operator p a b

{- | Build an expression `Data.Profunctor.Grammar.Grammar` from an
operator-precedence table: the invertible analogue of Parsec's
@buildExpressionParser@ and a multi-operator generalization of `chain1`
(which bakes in a single binary operator).

The table is a list of precedence levels ordered from *loosest* binding first
to *tightest* binding last (so the head level is the start symbol and the base
@term@ sits below the last level — this matches reading an operator cascade
top to bottom). Each level is a list of `Operator`s of equal precedence.

At one level, `Prefix`/`Postfix` operators bind tighter than the level's infix
operators (they wrap the term), and the infix operators must share a single
associativity — mixing `InfixL` and `InfixR` at the same level is ambiguous and
rejected. Multiple operators of the same kind (e.g. @+@ and @-@) may share a
level; they are threaded through one `difoldl` \/ `difoldr` so the fold peels
exactly this level's operators in both directions.

prop> buildExpressionG [] term = term
-}
buildExpressionG
  :: (Alternator p, Cochoice p)
  => [[Operator p a b]] {- ^ precedence table, loosest level first -}
  -> p a b {- ^ base term grammar -}
  -> p a b
buildExpressionG table term = foldr makeLevel term table

-- | Assemble one precedence level over the next-tighter grammar @term@.
makeLevel
  :: (Alternator p, Cochoice p)
  => [Operator p a b] -> p a b -> p a b
makeLevel ops term =
  let
    lefts'  = [ (pat, t) | InfixL  pat t <- ops ]
    rights' = [ (pat, t) | InfixR  pat t <- ops ]
    nons    = [ (pat, t) | Infix   pat t <- ops ]
    pres    = [ (pat, t) | Prefix  pat t <- ops ]
    posts   = [ (pat, t) | Postfix pat t <- ops ]
    termP   = postfixLevel posts (prefixLevel pres term)
  in case (rights', lefts', nons) of
      (rs@(_:_), [], []) -> infixLevelR rs termP
      ([], ls@(_:_), []) -> infixLevelL ls termP
      ([], [], ns@(_:_)) -> infixLevelN ns termP
      ([], [], [])       -> termP
      _ -> errorWithoutStackTrace
        "buildExpressionG: ambiguous associativity at one precedence level"

-- | Operator selector: parse/print the @i@-th symbol, carrying its index @i@,
-- so a homogeneous fold can recover which operator occurred.
opIx :: Alternator p => [p () ()] -> p Int Int
opIx toks = choice (zipWith (\i t -> only i >? t) [0 :: Int ..] toks)

-- | Combine a list of patterns into one index-tagged partial isomorphism:
-- matching tries each pattern in turn and tags the focus with its position;
-- building dispatches on that index. This is the one place the operator
-- identity is reified — the syntax tree need not carry an operator tag of its
-- own, so we synthesize a positional one and the fold threads it through.
indexedPattern :: [APartialIso s t a b] -> PartialIso s t (Int, a) (Int, b)
indexedPattern pats = partialIso
  (\s -> asum [ fmap ((,) i) (withPartialIso pat (\f _ -> f) s)
              | (i, pat) <- zip [0..] pats ])
  (\(i, b) -> withPartialIso (pats !! i) (\_ g -> g) b)

-- | Reshape an index-tagged pair @(i,(l,r))@ into the element each binary fold
-- expects: a left fold accumulates on the left, a right fold on the right.
ixBinL :: Iso (Int, (a, a)) (Int, (b, b)) (a, (Int, a)) (b, (Int, b))
ixBinL = iso (\(i,(l,r)) -> (l,(i,r))) (\(l,(i,r)) -> (i,(l,r)))

ixBinR :: Iso (Int, (a, a)) (Int, (b, b)) ((a, Int), a) ((b, Int), b)
ixBinR = iso (\(i,(l,r)) -> ((l,i),r)) (\((l,i),r) -> (i,(l,r)))

infixLevelL
  :: Alternator p
  => [(APartialIso a b (a, a) (b, b), p () ())] -> p a b -> p a b
infixLevelL ops sub =
  let (pats, toks) = unzip ops
  in difoldl (indexedPattern pats . ixBinL) >? (sub >*< manyP (opIx toks >*< sub))

infixLevelR
  :: Alternator p
  => [(APartialIso a b (a, a) (b, b), p () ())] -> p a b -> p a b
infixLevelR ops sub =
  let (pats, toks) = unzip ops
  in difoldr (indexedPattern pats . ixBinR) >? (manyP (sub >*< opIx toks) >*< sub)

infixLevelN
  :: (Alternator p, Cochoice p)
  => [(APartialIso a b (a, a) (b, b), p () ())] -> p a b -> p a b
infixLevelN ops sub =
  let (pats, toks) = unzip ops
  in ((indexedPattern pats . ixBinL) >?< (sub >*< (opIx toks >*< sub))) <|> sub

prefixLevel
  :: Alternator p
  => [(APartialIso a b a b, p () ())] -> p a b -> p a b
prefixLevel [] sub = sub
prefixLevel ops sub =
  let (pats, toks) = unzip ops
  in difoldr (indexedPattern pats) >? (manyP (opIx toks) >*< sub)

postfixLevel
  :: Alternator p
  => [(APartialIso a b a b, p () ())] -> p a b -> p a b
postfixLevel [] sub = sub
postfixLevel ops sub =
  let (pats, toks) = unzip ops
  in difoldl (indexedPattern pats . swapped) >? (sub >*< manyP (opIx toks))
