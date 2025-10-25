module Control.Lens.Grammar.Stream
  ( -- *
    IsStream
  , listed
  , streamed
  , stream
  , stream1
  , SepBy (..)
  , sepBy
  , noSep
  , chain
  , chain1
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.PartialIso
import Data.Profunctor
import Data.Profunctor.Distributor
import Data.Profunctor.Filtrator
import Data.Profunctor.Monoidal
import GHC.Exts

type IsStream s = (IsList s, AsEmpty s, Cons s s (Item s) (Item s))

listed :: (IsList s, IsList t, Item s ~ Item t) => Iso' s t
listed = iso (fromList . toList) (fromList . toList)

streamed :: (IsStream s, IsStream t, Item s ~ Item t) => Iso' s t
streamed = iso convertStream convertStream
  where
    convertStream s =
      maybe
        Empty
        (\(h,t) -> cons h (convertStream t))
        (uncons s)

{- |
prop> stream noSep = manyP
-}
stream
  :: (Distributor p, IsStream s, IsStream t)
  => SepBy (p () ())
  -> p (Item s) (Item t) -> p s t
stream (SepBy beg end sep) p = mapIso eotList $
  beg >* oneP >+< stream1 (sepBy sep) p *< end

{- |
prop> stream1 noSep p = p >*< manyP p
prop> _Cons >? stream1 noSep p = someP p
-}
stream1
  :: (Distributor p, IsStream s, IsStream t)
  => SepBy (p () ())
  -> p (Item s) (Item t) -> p (Item s, s) (Item t, t)
stream1 (SepBy beg end sep) p =
  beg >* p >*< stream (sepBy sep) p *< end

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
sepBy :: Monoidal p => p () () -> SepBy (p () ())
sepBy = SepBy oneP oneP

{- | A `SepBy` smart constructor for no separator,
beginning or ending delimiters. -}
noSep :: Monoidal p => SepBy (p () ())
noSep = sepBy oneP

chain
  :: (Alternator p, Filtrator p)
  => (forall x. x -> Either x x) -- `Left` or `Right` associate
  -> APartialIso a b (a,a) (b,b) -- ^ binary constructor pattern
  -> APartialIso a b () () -- ^ nilary constructor pattern
  -> SepBy (p () ()) -> p a b -> p a b
chain assoc c2 c0 sep p = 
  beginBy sep >*
  (c0 >?< oneP <|> chain1 assoc c2 (sepBy (separateBy sep)) p)
  *< endBy sep

chain1
  :: (Distributor p, Choice p, Cochoice p)
  => (forall x. x -> Either x x) -- `Left` or `Right` associate
  -> APartialIso a b (a,a) (b,b) -- ^ binary constructor pattern
  -> SepBy (p () ()) -> p a b -> p a b
chain1 = leftOrRight chainl1 chainr1
  where
    leftOrRight a b f = case f () of Left _ -> a; Right _ -> b
    chainl1 pat sep p =
      coPartialIso (difoldl (coPartialIso pat)) >?<
        beginBy sep >* p >*< manyP (separateBy sep >* p) *< endBy sep
    chainr1 pat sep p =
      coPartialIso (difoldr (coPartialIso pat)) >?<
        beginBy sep >* manyP (p *< separateBy sep) >*< p *< endBy sep
