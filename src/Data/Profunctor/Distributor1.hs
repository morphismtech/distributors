{-# LANGUAGE
ImpredicativeTypes
#-}

module Data.Profunctor.Distributor1
  ( -- | Constraints
    Monoidal1
  , Monoidal
  , Distributor1 ((>+<), optionalP, manyP, many1P)
  , Distributor (zeroP)
  , Alternator1 (alternate)
  , Alternator
    -- | Monoidal combinators
  , (>*<)
  , oneP
    -- | Mapping combinators
  , dimap2
  , dialt
    -- | Sequencing combinators
  , (>*)
  , (*<)
  , (>:<)
  , foreverP
  , replicateP'
  , replicateP_
  , someP
    -- | Separator combinators
  , manySep
  , many1Sep
  , someSep
  , By (beginBy, endBy, separator)
  , by
    -- | meander
  , meander
  ) where

import Control.Applicative
import Control.Arrow
import Control.Lens hiding ((<.>), (.>), (<.))
import Control.Lens.Internal.Context
import Control.Lens.Internal.FunList1
import Control.Lens.PartialIso
import Data.Functor.Alt
import Data.Profunctor
import Data.Profunctor.Partial1
import Data.Void

type Monoidal1 p = (Profunctor p, forall x. Apply (p x))

type Monoidal p = (Monoidal1 p, forall x. Applicative (p x))

class Monoidal p => Distributor1 p where
  (>+<) :: p a b -> p c d -> p (Either a c) (Either b d)
  infixr 1 >+<
  default (>+<)
    :: Alternator1 p
    => p a b -> p c d -> p (Either a c) (Either b d)
  x >+< y = alternate (Left x) <!> alternate (Right y)
  optionalP :: p a b -> p (Maybe a) (Maybe b)
  optionalP p = mapIso _M2E $ oneP >+< p
  manyP
    :: (AsEmpty t, Cons s s a a, Cons t t b b)
    => p a b -> p s t
  manyP p = mapIso _Stream $ oneP >+< many1P p
  many1P
    :: (AsEmpty t, Cons s s a a, Cons t t b b)
    => p a b -> p (a,s) (b,t)
  many1P p = p >*< manyP p

class Distributor1 p => Distributor p where
  zeroP :: p Void Void
  default zeroP :: (forall x. Alternative (p x)) => p Void Void
  zeroP = empty

class (Choice p, Distributor1 p, forall x. Alt (p x))
  => Alternator1 p where
    alternate
      :: Either (p a b) (p c d)
      -> p (Either a c) (Either b d)
    default alternate
      :: Cochoice p
      => Either (p a b) (p c d)
      -> p (Either a c) (Either b d)
    alternate = either
      (dimapMaybe (either Just (pure Nothing)) (Just . Left))
      (dimapMaybe (either (pure Nothing) Just) (Just . Right))

type Alternator p = (Alternator1 p, forall x. Alternative (p x))

someP
  :: (Choice p, Distributor1 p, AsEmpty t, Cons s s a a, Cons t t b b, Cons s t a b)
  => p a b -> p s t
someP p = _Cons >? many1P p

(>*<) :: Monoidal1 p => p a b -> p c d -> p (a,c) (b,d)
x >*< y = (,) <$> lmap fst x <.> lmap snd y

oneP :: Monoidal p => p () ()
oneP = pure ()

dimap2
  :: Monoidal1 p
  => (s -> a)
  -> (s -> c)
  -> (b -> d -> t)
  -> p a b -> p c d -> p s t
dimap2 f g h p q = dimap (f &&& g) (uncurry h) (p >*< q)

dialt
  :: Distributor1 p
  => (s -> Either a c)
  -> (b -> t)
  -> (d -> t)
  -> p a b -> p c d -> p s t
dialt f g h p q = dimap f (either g h) (p >+< q)

(>*) :: Monoidal1 p => p () c -> p a b -> p a b
x >* y = lmap (const ()) x .> y

(*<) :: Monoidal1 p => p a b -> p () c -> p a b
x *< y = x <. lmap (const ()) y

(>:<) :: (Choice p, Monoidal1 p, Cons s t a b) => p a b -> p s t -> p s t
ab >:< st = _Cons >? ab >*< st

foreverP :: Monoidal1 p => p () c -> p a b
foreverP p = let p' = p >* p' in p'

-- replicateP
--   :: (Monoidal p, Choice p, Cochoice p, Stream s t a b, Cons s t a b)
--   => Int -> p a b -> p s t
-- replicateP n _ | n <= 0 = _Null >?< oneP
-- replicateP n p = p >:< replicateP (n-1) p

replicateP'
  :: (Monoidal p, Choice p, AsEmpty s, Cons s s a a)
  => Int -> p a a -> p s s
replicateP' n _ | n <= 0 = _Empty >? oneP
replicateP' n p = p >:< replicateP' (n-1) p

replicateP_ :: Monoidal p => Int -> p () c -> p a ()
replicateP_ n _ | n <= 0 = pure ()
replicateP_ n p = p >* replicateP_ (n-1) p

meander
  :: (Choice p, Strong p, Monoidal1 p)
  => ATraversal s t a b -> p a b -> p s t
meander trav p =
  dimap (cloneTraversal trav sell) iextract (runMeander p)
    where
      runMeander
        :: (Choice p, Strong p, Monoidal1 p)
        => p u v -> p (Bazaar (->) u w x) (Bazaar (->) v w x)
      runMeander q = mapIso funList $ right' (q >*< runMeander q)

manySep
  :: (Distributor1 p, AsEmpty t, Cons s s a a, Cons t t b b)
  => By p -> p a b -> p s t
manySep (By {separator = comma, beginBy = beg, endBy = end}) p =
  mapIso _Stream $ beg >* (oneP >+< p >*< manyP (comma >* p)) *< end

many1Sep
  :: (Distributor1 p, AsEmpty t, Cons s s a a, Cons t t b b)
  => By p -> p a b -> p (a,s) (b,t)
many1Sep (By {separator = comma, beginBy = beg, endBy = end}) p =
  beg >* p >*< manyP (comma >* p) *< end

someSep
  :: ( Distributor1 p
     , Choice p
     , AsEmpty t
     , Cons s s a a
     , Cons t t b b
     , Cons s t a b
     )
  => By p -> p a b -> p s t
someSep s p = _Cons >? many1Sep s p

{- | Used to parse multiple times, delimited `by` a separator,
a `beginBy`, and an `endBy`. -}
data By p = By
  { beginBy :: p () ()
  , endBy :: p () ()
  , separator :: p () ()
  }

{- | A default `By` which can be modified by updating
`beginBy`, or `endBy` fields -}
by :: Monoidal p => p () () -> By p
by = By oneP oneP

{- | The `_Stream` `Control.Lens.Iso.Iso` with a sum of products. -}
_Stream
  :: (AsEmpty t, Cons s s a a, Cons t t b b)
  => Iso s t (Either () (a,s)) (Either () (b,t))
_Stream = _HeadTailMay . _M2E

{- | `_HeadTailMay` `Control.Lens.Iso.Iso` with `Maybe` a pair. -}
_HeadTailMay
  :: (AsEmpty t, Cons s s a a, Cons t t b b)
  => Iso s t (Maybe (a,s)) (Maybe (b,t))
_HeadTailMay = iso (preview _Cons) (maybe Empty (uncurry cons))
