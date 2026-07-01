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
    -- * Operator Expressions
  , Operator (..)
  , withOperators
  ) where

import Control.Applicative ((<|>))
import Control.Lens
import Control.Lens.PartialIso
import Control.Lens.Grammar.Symbol
import Data.Foldable (asum)
import Data.Maybe (listToMaybe)
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

data Operator p a b where
  Infix :: APartialIso a b (a,a) (b,b) -> p () () -> Operator p a b
  InfixL :: APartialIso a b (a,a) (b,b) -> p () () -> Operator p a b
  InfixR :: APartialIso a b (a,a) (b,b) -> p () () -> Operator p a b
  Prefix :: APartialIso a b a b -> p () () -> Operator p a b
  Postfix :: APartialIso a b a b -> p () () -> Operator p a b

{- | Build an expression `Alternator` from a table of `Operator`s and
an atomic term `Alternator`, analagous to @buildExpressionParser@ from
[parsec](https://hackage.haskell.org/package/parsec).

The operator table is a list of list of operators, ordered from highest to lowest precedence.
Each level is a list of `Operator`s which share precedence.
Within a level, `InfixL`, `InfixR` & `Infix` set left, right & non-associativity for binary operators,
while `Prefix` & `Postfix` are for unary operators. -}
withOperators
  :: Alternator p
  => [[Operator p a b]] -- ^ operator table
  -> p a b -- ^ atomic term
  -> p a b -- ^ expression
withOperators table p = foldl makeLevel p table
  where
    makeLevel term ops =
      let
        (nas, las, ras, pres, posts) =
          foldr splitOp ([],[],[],[],[]) ops
        termP = withPostP posts (withPreP pres term)
      in
        case (nas, las, ras) of
          (_,  [], []) -> infixNP nas termP
          ([], _,  []) -> infixLP manyP las termP
          ([], [], _ ) -> infixRP manyP ras termP
          _            ->
            infixRP someP ras termP
            <|> infixLP someP las termP
            <|> infixNP nas termP

    splitOp oper (nas, las, ras, pres, posts) = case oper of
      Infix   pat sym -> ((pat,sym):nas, las, ras, pres, posts)
      InfixL  pat sym -> (nas, (pat,sym):las, ras, pres, posts)
      InfixR  pat sym -> (nas, las, (pat,sym):ras, pres, posts)
      Prefix  pat sym -> (nas, las, ras, (pat,sym):pres, posts)
      Postfix pat sym -> (nas, las, ras, pres, (pat,sym):posts)

    tagSepP syms = choice [only i >? sym | (i, sym) <- zip [0 :: Int ..] syms]

    withPreP ops inner =
      difoldr (partialIso fwd bwd) >? manyP (tagSepP (snd <$> ops)) >*< inner
      where
        fns = [withPartialIso pat (,) | (pat, _) <- ops]
        fwd x = asum
          [ (\y -> (i,y)) <$> f x | (i, (f,_)) <- zip [0 :: Int ..] fns ]
        bwd (i,y) = case drop i fns of
          (_,g):_ -> g y
          [] -> Nothing

    withPostP ops inner =
      difoldl (partialIso fwd bwd) >? inner >*< manyP (tagSepP (snd <$> ops))
      where
        fns = [withPartialIso pat (,) | (pat, _) <- ops]
        fwd x = asum
          [ (\y -> (y,i)) <$> f x | (i, (f,_)) <- zip [0 :: Int ..] fns ]
        bwd (y,i) = case drop i fns of
          (_,g):_ -> g y
          [] -> Nothing

    infixNP ops term =
      difoldl (partialIso fwd bwd) >? term >*< oneTail
      where
        oneTail =
          iso listToMaybe (maybe [] pure) >~
            optionalP (tagSepP (snd <$> ops) >*< term)
        fns = [withPartialIso pat (,) | (pat, _) <- ops]
        fwd x = asum
          [ (\(l,r) -> (l,(i,r))) <$> f x
          | (i, (f,_)) <- zip [0 :: Int ..] fns ]
        bwd (l,(i,r)) = case drop i fns of
          (_,g):_ -> g (l,r)
          [] -> Nothing

    -- Left-associative applications, folded to the left. The @rep@ tail
    -- combinator is `manyP` for a pure-left level (the empty tail folds back
    -- to the bare term) or `someP` in a mixed level (an operator is required).
    infixLP
      :: Alternator p
      => (p (Int,a) (Int,b) -> p [(Int,a)] [(Int,b)])
      -> [(APartialIso a b (a,a) (b,b), p () ())] -> p a b -> p a b
    infixLP rep ops term =
      difoldl (partialIso fwd bwd) >?
        term >*< rep (tagSepP (snd <$> ops) >*< term)
      where
        fns = [withPartialIso pat (,) | (pat, _) <- ops]
        fwd x = asum
          [ (\(l,r) -> (l,(i,r))) <$> f x
          | (i, (f,_)) <- zip [0 :: Int ..] fns ]
        bwd (l,(i,r)) = case drop i fns of
          (_,g):_ -> g (l,r)
          [] -> Nothing

    -- Right-associative applications, folded to the right. As with `infixLP`,
    -- @rep@ is `manyP` for a pure-right level or `someP` in a mixed level.
    infixRP
      :: Alternator p
      => (p (a,Int) (b,Int) -> p [(a,Int)] [(b,Int)])
      -> [(APartialIso a b (a,a) (b,b), p () ())] -> p a b -> p a b
    infixRP rep ops term =
      difoldr (partialIso fwd bwd) >?
        rep (term >*< tagSepP (snd <$> ops)) >*< term
      where
        fns = [withPartialIso pat (,) | (pat, _) <- ops]
        fwd x = asum
          [ (\(l,r) -> ((l,i),r)) <$> f x
          | (i, (f,_)) <- zip [0 :: Int ..] fns ]
        bwd ((l,i),r) = case drop i fns of
          (_,g):_ -> g (l,r)
          [] -> Nothing
