{-|
Module      : Data.Profunctor.Separator
Description : distributors
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable
-}

module Data.Profunctor.Separator
  ( SepBy (..)
  , sepBy
  , noSep
  , several
  , several1
  , chain
  , chain1
  , intercalateP
  ) where

import Control.Lens
import Control.Lens.PartialIso
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
setting the `separateBy` field,
with no beginning or ending delimitors,
except by updating `beginBy` or `endBy` fields. -}
sepBy :: Applicative p => p () -> SepBy (p ())
sepBy = SepBy (pure ()) (pure ())

-- sepWith :: (Monoidal p, TerminalSymbol c (p () ())) => 

{- | A `SepBy` smart constructor for no separator,
beginning or ending delimiters. -}
noSep :: Monoidal p => SepBy (p () ())
noSep = sepBy oneP

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
