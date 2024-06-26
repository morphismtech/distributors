module Control.Lens.Stream
  ( Nil (_Nil), nil, Null (_Null, _NotNull)
  , SimpleStream (_All, _AllNot, _Span, _Break)
  , _Stream, _HeadTailMay, _ConvertStream
  , Stream (_LengthIs, _SplitAt), _HeadTail
  , difoldl1, difoldr1, difoldl, difoldr, difoldl', difoldr'
  ) where

import Data.Profunctor
import           Control.Applicative (ZipList(..))
import Control.Lens
import Control.Lens.PartialIso

import qualified Data.ByteString      as StrictB
import qualified Data.ByteString.Lazy as LazyB
import qualified Data.Sequence as Seq
import           Data.Sequence (Seq)
import qualified Data.Text      as StrictT
import qualified Data.Text.Lazy as LazyT
import           Data.Vector (Vector)
import qualified Data.Vector.Generic as Vector
import           Data.Vector.Storable (Storable)
import qualified Data.Vector.Storable as Storable (Vector)
import           Data.Vector.Primitive (Prim)
import qualified Data.Vector.Primitive as Prim (Vector)
import           Data.Vector.Unboxed (Unbox)
import qualified Data.Vector.Unboxed as Unbox (Vector)
import           Data.Word

class Nil s a | s -> a where
  _Nil :: Prism' s ()
instance Nil (Maybe a) a where
  _Nil = _Nothing
instance Nil (Either () a) a where
  _Nil = _Left
emptyPrism :: (t -> Bool) -> t -> Prism' t ()
emptyPrism null' empty' = prism (pure empty') $ \x ->
  if null' x then Right () else Left x
instance Nil [a] a where
  _Nil = emptyPrism null []
instance Nil (ZipList a) a where
  _Nil = iso getZipList ZipList . _Nil
instance Nil (Seq a) a where
  _Nil = emptyPrism Seq.null Seq.empty
instance Nil StrictB.ByteString Word8 where
  _Nil = emptyPrism StrictB.null StrictB.empty
instance Nil LazyB.ByteString Word8 where
  _Nil = emptyPrism LazyB.null LazyB.empty
instance Nil StrictT.Text Char where
  _Nil = emptyPrism StrictT.null StrictT.empty
instance Nil LazyT.Text Char where
  _Nil = emptyPrism LazyT.null LazyT.empty
instance Nil (Vector a) a where
  _Nil = emptyPrism Vector.null Vector.empty
instance Prim a => Nil (Prim.Vector a) a where
  _Nil = emptyPrism Vector.null Vector.empty
instance Storable a => Nil (Storable.Vector a) a where
  _Nil = emptyPrism Vector.null Vector.empty
instance Unbox a => Nil (Unbox.Vector a) a where
  _Nil = emptyPrism Vector.null Vector.empty

nil :: Nil s a => s
nil = review _Nil ()

class
  ( Nil s a
  , Nil t b
  , Null s s a a
  , Null t t b b
  ) => Null s t a b | b s -> t, a t -> s where
  _Null :: PartialIso s t () ()
  _NotNull :: PartialIso s t s t
instance Null (Maybe a) (Maybe b) a b where
  _Null = partialIso
    (maybe (Just ()) (pure Nothing))
    (pure (Just Nothing))
  _NotNull = partialIso nonemp nonemp where
    nonemp Nothing = Nothing
    nonemp (Just x) = Just (Just x)
instance Null (Either () a) (Either () b) a b where
  _Null = partialIso
    (either Just (pure Nothing))
    (pure (Just (Left ())))
  _NotNull = partialIso nonemp nonemp where
    nonemp (Left ()) = Nothing
    nonemp (Right x) = Just (Right x)
emptyIso :: (s -> Bool) -> t -> PartialIso s t () ()
emptyIso null' empty' = partialIso
  (\l -> if null' l then Just () else Nothing)
  (pure (Just empty'))
neIso :: (s -> Bool) -> (t -> Bool) -> PartialIso s t s t
neIso null0 null1 = partialIso (ne null0) (ne null1)
  where
    ne null' l = if not (null' l) then Just l else Nothing
instance Null [a] [b] a b where
  _Null = emptyIso null []
  _NotNull = neIso null null
instance Null (ZipList a) (ZipList b) a b where
  _Null = iso getZipList ZipList . _Null
  _NotNull = iso getZipList ZipList . _NotNull . iso ZipList getZipList
instance Null (Seq a) (Seq b) a b where
  _Null = emptyIso Seq.null Seq.empty
  _NotNull = neIso Seq.null Seq.null
instance Null StrictB.ByteString StrictB.ByteString Word8 Word8 where
  _Null = emptyIso StrictB.null StrictB.empty
  _NotNull = neIso StrictB.null StrictB.null
instance Null LazyB.ByteString LazyB.ByteString Word8 Word8 where
  _Null = emptyIso LazyB.null LazyB.empty
  _NotNull = neIso LazyB.null LazyB.null
instance Null StrictT.Text StrictT.Text Char Char where
  _Null = emptyIso StrictT.null StrictT.empty
  _NotNull = neIso StrictT.null StrictT.null
instance Null LazyT.Text LazyT.Text Char Char where
  _Null = emptyIso LazyT.null LazyT.empty
  _NotNull = neIso LazyT.null LazyT.null
instance Null (Vector a) (Vector b) a b where
  _Null = emptyIso Vector.null Vector.empty
  _NotNull = neIso Vector.null Vector.null
instance (Prim a, Prim b) => Null (Prim.Vector a) (Prim.Vector b) a b where
  _Null = emptyIso Vector.null Vector.empty
  _NotNull = neIso Vector.null Vector.null
instance (Storable a, Storable b) => Null (Storable.Vector a) (Storable.Vector b) a b where
  _Null = emptyIso Vector.null Vector.empty
  _NotNull = neIso Vector.null Vector.null
instance (Unbox a, Unbox b) => Null (Unbox.Vector a) (Unbox.Vector b) a b where
  _Null = emptyIso Vector.null Vector.empty
  _NotNull = neIso Vector.null Vector.null

class (Monoid s, Nil s a, Cons s s a a) => SimpleStream s a where
  _All :: (a -> Bool) -> PartialIso' s s
  _AllNot :: (a -> Bool) -> PartialIso' s s
  _Span :: (a -> Bool) -> PartialIso' s (s,s)
  _Break :: (a -> Bool) -> PartialIso' s (s,s)
instance SimpleStream [a] a where
  _All f = partialIso every every where
    every list = if all f list then Just list else Nothing
  _AllNot f = partialIso everyNot everyNot where
    everyNot list = if all (not . f) list then Just list else Nothing
  _Span f = iso (span f) (uncurry (<>)) . crossPartialIso (_All f) id
  _Break f = iso (break f) (uncurry (<>)) . crossPartialIso (_AllNot f) id
instance SimpleStream (Seq a) a where
  _All f = partialIso every every where
    every list = if all f list then Just list else Nothing
  _AllNot f = partialIso everyNot everyNot where
    everyNot list = if all (not . f) list then Just list else Nothing
  _Span f = iso (Seq.spanl f) (uncurry (<>)) . crossPartialIso (_All f) id
  _Break f = iso (Seq.breakl f) (uncurry (<>)) . crossPartialIso (_AllNot f) id
instance SimpleStream (Vector a) a where
  _All f = partialIso every every where
    every list = if all f list then Just list else Nothing
  _AllNot f = partialIso everyNot everyNot where
    everyNot list = if all (not . f) list then Just list else Nothing
  _Span f = iso (Vector.span f) (uncurry (<>)) . crossPartialIso (_All f) id
  _Break f = iso (Vector.break f) (uncurry (<>)) . crossPartialIso (_AllNot f) id
instance Prim a => SimpleStream (Prim.Vector a) a where
  _All f = partialIso every every where
    every list = if Vector.all f list then Just list else Nothing
  _AllNot f = partialIso everyNot everyNot where
    everyNot list = if Vector.all (not . f) list then Just list else Nothing
  _Span f = iso (Vector.span f) (uncurry (<>)) . crossPartialIso (_All f) id
  _Break f = iso (Vector.break f) (uncurry (<>)) . crossPartialIso (_AllNot f) id
instance Storable a => SimpleStream (Storable.Vector a) a where
  _All f = partialIso every every where
    every list = if Vector.all f list then Just list else Nothing
  _AllNot f = partialIso everyNot everyNot where
    everyNot list = if Vector.all (not . f) list then Just list else Nothing
  _Span f = iso (Vector.span f) (uncurry (<>)) . crossPartialIso (_All f) id
  _Break f = iso (Vector.break f) (uncurry (<>)) . crossPartialIso (_AllNot f) id
instance Unbox a => SimpleStream (Unbox.Vector a) a where
  _All f = partialIso every every where
    every list = if Vector.all f list then Just list else Nothing
  _AllNot f = partialIso everyNot everyNot where
    everyNot list = if Vector.all (not . f) list then Just list else Nothing
  _Span f = iso (Vector.span f) (uncurry (<>)) . crossPartialIso (_All f) id
  _Break f = iso (Vector.break f) (uncurry (<>)) . crossPartialIso (_AllNot f) id
instance SimpleStream StrictB.ByteString Word8 where
  _All f = partialIso every every where
    every list = if StrictB.all f list then Just list else Nothing
  _AllNot f = partialIso everyNot everyNot where
    everyNot list = if StrictB.all (not . f) list then Just list else Nothing
  _Span f = iso (StrictB.span f) (uncurry (<>)) . crossPartialIso (_All f) id
  _Break f = iso (StrictB.break f) (uncurry (<>)) . crossPartialIso (_AllNot f) id
instance SimpleStream LazyB.ByteString Word8 where
  _All f = partialIso every every where
    every list = if LazyB.all f list then Just list else Nothing
  _AllNot f = partialIso everyNot everyNot where
    everyNot list = if LazyB.all (not . f) list then Just list else Nothing
  _Span f = iso (LazyB.span f) (uncurry (<>)) . crossPartialIso (_All f) id
  _Break f = iso (LazyB.break f) (uncurry (<>)) . crossPartialIso (_AllNot f) id
instance SimpleStream StrictT.Text Char where
  _All f = partialIso every every where
    every list = if StrictT.all f list then Just list else Nothing
  _AllNot f = partialIso everyNot everyNot where
    everyNot list = if StrictT.all (not . f) list then Just list else Nothing
  _Span f = iso (StrictT.span f) (uncurry (<>)) . crossPartialIso (_All f) id
  _Break f = iso (StrictT.break f) (uncurry (<>)) . crossPartialIso (_AllNot f) id
instance SimpleStream LazyT.Text Char where
  _All f = partialIso every every where
    every list = if LazyT.all f list then Just list else Nothing
  _AllNot f = partialIso everyNot everyNot where
    everyNot list = if LazyT.all (not . f) list then Just list else Nothing
  _Span f = iso (LazyT.span f) (uncurry (<>)) . crossPartialIso (_All f) id
  _Break f = iso (LazyT.break f) (uncurry (<>)) . crossPartialIso (_AllNot f) id

_Stream
  :: (SimpleStream s a, SimpleStream t b)
  => Iso s t (Either () (a,s)) (Either () (b,t))
_Stream = _HeadTailMay . _M2E

_HeadTailMay
  ::  (SimpleStream s a, SimpleStream t b)
  => Iso s t (Maybe (a,s)) (Maybe (b,t))
_HeadTailMay = iso (preview _Cons) (maybe nil (uncurry cons))

_ConvertStream :: (SimpleStream s a, SimpleStream t a) => Iso' s t
_ConvertStream = iso convertStream convertStream
  where
    convertStream s =
      maybe
        nil
        (\(h,t) -> cons h (convertStream t))
        (view _HeadTailMay s)

class
  ( Null s t a b
  , Cons s t a b
  , SimpleStream s a
  , SimpleStream t b
  ) => Stream s t a b where
  _LengthIs :: (Int -> Bool) -> PartialIso s t s t
  _SplitAt :: Int -> PartialIso s t (s,s) (t,t)
instance Stream [a] [b] a b where
  _LengthIs f = partialIso lengthen lengthen where
    lengthen :: [c] -> Maybe [c]
    lengthen list = if f (length list) then Just list else Nothing
  _SplitAt n
    = _LengthIs (>= n)
    . iso (splitAt n) (uncurry (<>))
    . crossPartialIso (_LengthIs (== max 0 n)) id
instance Stream (Seq a) (Seq b) a b where
  _LengthIs f = partialIso lengthen lengthen where
    lengthen :: Seq c -> Maybe (Seq c)
    lengthen list = if f (Seq.length list) then Just list else Nothing
  _SplitAt n
    = _LengthIs (>= n)
    . iso (Seq.splitAt n) (uncurry (<>))
    . crossPartialIso (_LengthIs (== max 0 n)) id
instance Stream (Vector a) (Vector b) a b where
  _LengthIs f = partialIso lengthen lengthen where
    lengthen :: Vector c -> Maybe (Vector c)
    lengthen list = if f (Vector.length list) then Just list else Nothing
  _SplitAt n
    = _LengthIs (>= n)
    . iso (Vector.splitAt n) (uncurry (<>))
    . crossPartialIso (_LengthIs (== max 0 n)) id
instance (Storable a, Storable b)
  => Stream (Storable.Vector a) (Storable.Vector b) a b where
  _LengthIs f = partialIso lengthen lengthen where
    lengthen :: Storable c => Storable.Vector c -> Maybe (Storable.Vector c)
    lengthen list = if f (Vector.length list) then Just list else Nothing
  _SplitAt n
    = _LengthIs (>= n)
    . iso (Vector.splitAt n) (uncurry (<>))
    . crossPartialIso (_LengthIs (== max 0 n)) id
instance (Unbox a, Unbox b)
  => Stream (Unbox.Vector a) (Unbox.Vector b) a b where
  _LengthIs f = partialIso lengthen lengthen where
    lengthen :: Unbox c => Unbox.Vector c -> Maybe (Unbox.Vector c)
    lengthen list = if f (Vector.length list) then Just list else Nothing
  _SplitAt n
    = _LengthIs (>= n)
    . iso (Vector.splitAt n) (uncurry (<>))
    . crossPartialIso (_LengthIs (== max 0 n)) id
instance (Prim a, Prim b)
  => Stream (Prim.Vector a) (Prim.Vector b) a b where
  _LengthIs f = partialIso lengthen lengthen where
    lengthen :: Prim c => Prim.Vector c -> Maybe (Prim.Vector c)
    lengthen list = if f (Vector.length list) then Just list else Nothing
  _SplitAt n
    = _LengthIs (>= n)
    . iso (Vector.splitAt n) (uncurry (<>))
    . crossPartialIso (_LengthIs (== max 0 n)) id
instance Stream StrictB.ByteString StrictB.ByteString Word8 Word8 where
  _LengthIs f = partialIso lengthen lengthen where
    lengthen :: StrictB.ByteString -> Maybe StrictB.ByteString
    lengthen list = if f (StrictB.length list) then Just list else Nothing
  _SplitAt n
    = _LengthIs (>= n)
    . iso (StrictB.splitAt n) (uncurry (<>))
    . crossPartialIso (_LengthIs (== max 0 n)) id
instance Stream LazyB.ByteString LazyB.ByteString Word8 Word8 where
  _LengthIs f = partialIso lengthen lengthen where
    lengthen :: LazyB.ByteString -> Maybe LazyB.ByteString
    lengthen list =
      if f (fromIntegral (LazyB.length list))
      then Just list else Nothing
  _SplitAt n
    = _LengthIs (>= n)
    . iso (LazyB.splitAt (fromIntegral n)) (uncurry (<>))
    . crossPartialIso (_LengthIs (== max 0 n)) id
instance Stream StrictT.Text StrictT.Text Char Char where
  _LengthIs f = partialIso lengthen lengthen where
    lengthen :: StrictT.Text -> Maybe StrictT.Text
    lengthen list = if f (StrictT.length list) then Just list else Nothing
  _SplitAt n
    = _LengthIs (>= n)
    . iso (StrictT.splitAt n) (uncurry (<>))
    . crossPartialIso (_LengthIs (== max 0 n)) id
instance Stream LazyT.Text LazyT.Text Char Char where
  _LengthIs f = partialIso lengthen lengthen where
    lengthen :: LazyT.Text -> Maybe LazyT.Text
    lengthen list =
      if f (fromIntegral (LazyT.length list))
      then Just list else Nothing
  _SplitAt n
    = _LengthIs (>= n)
    . iso (LazyT.splitAt (fromIntegral n)) (uncurry (<>))
    . crossPartialIso (_LengthIs (== max 0 n)) id

_HeadTail
  :: Stream s t a b
  => PartialIso s t (a,s) (b,t)
_HeadTail = _NotNull . _HeadTailMay . _Just

difoldl1
  :: Cons s t a b
  => APartialIso (c,a) (d,b) c d
  -> Iso (c,s) (d,t) (c,s) (d,t)
difoldl1 i =
  let
    associate = iso
      (\(c,(a,s)) -> ((c,a),s))
      (\((d,b),t) -> (d,(b,t)))
    step
      = crossPartialIso id _Cons
      . associate
      . crossPartialIso i id
  in iterating step

difoldr1
  :: Cons s t a b
  => APartialIso (a,c) (b,d) c d
  -> Iso (s,c) (t,d) (s,c) (t,d)
difoldr1 i =
  let
    reorder = iso
      (\((a,s),c) -> (s,(a,c)))
      (\(t,(b,d)) -> ((b,t),d))
    step
      = crossPartialIso _Cons id
      . reorder
      . crossPartialIso id i
  in iterating step

difoldl
  :: Stream s t a b
  => APartialIso (c,a) (d,b) c d
  -> PartialIso (c,s) (d,t) c d
difoldl i =
  let
    unit' = iso
      (\(a,()) -> a)
      (\a -> (a,()))
  in
    difoldl1 i
    . crossPartialIso id _Null
    . unit'

difoldl'
  :: SimpleStream s a
  => APrism' (c,a) c
  -> Prism' (c,s) c
difoldl' i =
  let
    unit' = iso
      (\(a,()) -> a)
      (\a -> (a,()))
  in
    difoldl1 (clonePrism i)
    . aside _Nil
    . unit'

difoldr
  :: Stream s t a b
  => APartialIso (a,c) (b,d) c d
  -> PartialIso (s,c) (t,d) c d
difoldr i =
  let
    unit' = iso
      (\((),c) -> c)
      (\d -> ((),d))
  in
    difoldr1 i
    . crossPartialIso _Null id
    . unit'

difoldr'
  :: SimpleStream s a
  => APrism' (a,c) c
  -> Prism' (s,c) c
difoldr' i =
  let
    unit' = iso
      (\((),c) -> c)
      (\c -> ((),c))
    asideFst k =
      withPrism k $ \bt seta ->
        prism (first' bt) $ \(s,e) ->
          case seta s of
            Left t -> Left  (t,e)
            Right a -> Right (a,e)
  in
    difoldr1 (clonePrism i)
    . asideFst _Nil
    . unit'
