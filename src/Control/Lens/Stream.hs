{- |
Module      :  Control.Lens.Stream
Description :  stream optics
Copyright   :  (C) 2024 - Eitan Chatav
License     :  BSD-style (see the file LICENSE)
Maintainer  :  Eitan Chatav <eitan.chatav@gmail.com>
Stability   :  provisional
Portability :  non-portable

This module defines optics-style interfaces for
types which are list-like streams of tokens.
-}
module Control.Lens.Stream
  ( -- * Stream
    Stream
  , Stream'
    -- * Optics
  , _Stream
  , _HeadTailMay
  , _Tokens
  , _HeadTail
  , _Null
  , _NotNull
    -- * Streaming
  , Streaming' (..)
  , Streaming (..)
    -- * Fold/Unfold
  , difoldl1
  , difoldr1
  , difoldl
  , difoldr
  , difoldl'
  , difoldr'
  ) where

-- import Control.Applicative (ZipList(..))
import Control.Lens
import Control.Lens.PartialIso
import qualified Data.ByteString as StrictB
import qualified Data.ByteString.Lazy as LazyB
import Data.Profunctor
import qualified Data.Sequence as Seq
import Data.Sequence (Seq)
import qualified Data.Text as StrictT
import qualified Data.Text.Lazy as LazyT
import Data.Vector (Vector)
import qualified Data.Vector.Generic as Vector
import Data.Vector.Storable (Storable)
import qualified Data.Vector.Storable as Storable (Vector)
import Data.Vector.Unboxed (Unbox)
import qualified Data.Vector.Unboxed as Unbox (Vector)
import Data.Word

{- | `Stream` @s@ @t@ @a@ @b@ means
that @s@ is a stream of @a@-tokens,
and @t@ is a stream of @b@-tokens.
-}
type Stream s t a b = (Stream' s a, Stream' t b)

{- | A `Stream'` is a `Monoid` with `_Empty` and `_Cons`
`Control.Lens.Prism.Prism'`s.

prop> Empty = mempty
prop> a `cons` (b <> c) = (a `cons` b) <> c
-}
type Stream' s a = (Monoid s, AsEmpty s, Cons s s a a)

{- | A class for stream types, with a monomorphic token type,
allowing partial bidirectional pattern matching
with a list-like interface. -}
class Stream' s a => Streaming' s a where
  {- | All tokens satisfy the predicate. -}
  _All :: (a -> Bool) -> PartialIso' s s
  {- | No tokens satisfy the predicate. -}
  _None :: (a -> Bool) -> PartialIso' s s
  {- | A tuple where first element is
  the longest prefix (optionP empty) of tokens
  that satisfy the predicate and second element is
  the remainder of the stream. -}
  _Span :: (a -> Bool) -> PartialIso' s (s,s)
  {- | A tuple where first element is
  the longest prefix (optionP empty) of tokens
  that don't satisfy the predicate and second element is
  the remainder of the stream. -}
  _Break :: (a -> Bool) -> PartialIso' s (s,s)
instance Streaming' [a] a where
  _All f = partialIso every every where
    every list = if all f list then Just list else Nothing
  _None f = partialIso everyNot everyNot where
    everyNot list = if all (not . f) list then Just list else Nothing
  _Span f = iso (span f) (uncurry (<>)) . crossPartialIso (_All f) id
  _Break f = iso (break f) (uncurry (<>)) . crossPartialIso (_None f) id
instance Streaming' (Seq a) a where
  _All f = partialIso every every where
    every list = if all f list then Just list else Nothing
  _None f = partialIso everyNot everyNot where
    everyNot list = if all (not . f) list then Just list else Nothing
  _Span f = iso (Seq.spanl f) (uncurry (<>)) . crossPartialIso (_All f) id
  _Break f = iso (Seq.breakl f) (uncurry (<>)) . crossPartialIso (_None f) id
instance Streaming' (Vector a) a where
  _All f = partialIso every every where
    every list = if all f list then Just list else Nothing
  _None f = partialIso everyNot everyNot where
    everyNot list = if all (not . f) list then Just list else Nothing
  _Span f = iso (Vector.span f) (uncurry (<>)) . crossPartialIso (_All f) id
  _Break f = iso (Vector.break f) (uncurry (<>)) . crossPartialIso (_None f) id
instance Storable a => Streaming' (Storable.Vector a) a where
  _All f = partialIso every every where
    every list = if Vector.all f list then Just list else Nothing
  _None f = partialIso everyNot everyNot where
    everyNot list = if Vector.all (not . f) list then Just list else Nothing
  _Span f = iso (Vector.span f) (uncurry (<>)) . crossPartialIso (_All f) id
  _Break f = iso (Vector.break f) (uncurry (<>)) . crossPartialIso (_None f) id
instance Unbox a => Streaming' (Unbox.Vector a) a where
  _All f = partialIso every every where
    every list = if Vector.all f list then Just list else Nothing
  _None f = partialIso everyNot everyNot where
    everyNot list = if Vector.all (not . f) list then Just list else Nothing
  _Span f = iso (Vector.span f) (uncurry (<>)) . crossPartialIso (_All f) id
  _Break f = iso (Vector.break f) (uncurry (<>)) . crossPartialIso (_None f) id
instance Streaming' StrictB.ByteString Word8 where
  _All f = partialIso every every where
    every list = if StrictB.all f list then Just list else Nothing
  _None f = partialIso everyNot everyNot where
    everyNot list = if StrictB.all (not . f) list then Just list else Nothing
  _Span f = iso (StrictB.span f) (uncurry (<>)) . crossPartialIso (_All f) id
  _Break f = iso (StrictB.break f) (uncurry (<>)) . crossPartialIso (_None f) id
instance Streaming' LazyB.ByteString Word8 where
  _All f = partialIso every every where
    every list = if LazyB.all f list then Just list else Nothing
  _None f = partialIso everyNot everyNot where
    everyNot list = if LazyB.all (not . f) list then Just list else Nothing
  _Span f = iso (LazyB.span f) (uncurry (<>)) . crossPartialIso (_All f) id
  _Break f = iso (LazyB.break f) (uncurry (<>)) . crossPartialIso (_None f) id
instance Streaming' StrictT.Text Char where
  _All f = partialIso every every where
    every list = if StrictT.all f list then Just list else Nothing
  _None f = partialIso everyNot everyNot where
    everyNot list = if StrictT.all (not . f) list then Just list else Nothing
  _Span f = iso (StrictT.span f) (uncurry (<>)) . crossPartialIso (_All f) id
  _Break f = iso (StrictT.break f) (uncurry (<>)) . crossPartialIso (_None f) id
instance Streaming' LazyT.Text Char where
  _All f = partialIso every every where
    every list = if LazyT.all f list then Just list else Nothing
  _None f = partialIso everyNot everyNot where
    everyNot list = if LazyT.all (not . f) list then Just list else Nothing
  _Span f = iso (LazyT.span f) (uncurry (<>)) . crossPartialIso (_All f) id
  _Break f = iso (LazyT.break f) (uncurry (<>)) . crossPartialIso (_None f) id

{- | The `_Stream` `Control.Lens.Iso.Iso` with a sum of products. -}
_Stream
  :: Stream s t a b
  => Iso s t (Either () (a,s)) (Either () (b,t))
_Stream = _HeadTailMay . _M2E

{- | `_HeadTailMay` `Control.Lens.Iso.Iso` with `Maybe` a pair. -}
_HeadTailMay
  :: Stream s t a b
  => Iso s t (Maybe (a,s)) (Maybe (b,t))
_HeadTailMay = iso (preview _Cons) (maybe Empty (uncurry cons))

{- | `_Tokens` `Control.Lens.Iso.Iso` between
streams with the same token type. -}
_Tokens :: Stream s t c c => Iso' s t
_Tokens = iso convertStream convertStream
  where
    convertStream s =
      maybe
        Empty
        (\(h,t) -> cons h (convertStream t))
        (view _HeadTailMay s)

{- | A class for stream types, with a potentially polymorphic token type,
allowing partial bidirectional pattern matching with a list-like interface. -}
class Stream s t a b => Streaming s t a b where
  {- | Matches on streams which satisfy a predicate on their length. -}
  _LengthIs :: (Int -> Bool) -> PartialIso s t s t
  {- | A tuple where first element is
  the stream of tokens of given length and second element is
  the remainder of the stream. -}
  _SplitAt :: Int -> PartialIso s t (s,s) (t,t)
instance Streaming [a] [b] a b where
  _LengthIs f = partialIso lengthen lengthen where
    lengthen :: [c] -> Maybe [c]
    lengthen list = if f (length list) then Just list else Nothing
  _SplitAt n
    = _LengthIs (>= n)
    . iso (splitAt n) (uncurry (<>))
    . crossPartialIso (_LengthIs (== max 0 n)) id
instance Streaming (Seq a) (Seq b) a b where
  _LengthIs f = partialIso lengthen lengthen where
    lengthen :: Seq c -> Maybe (Seq c)
    lengthen list = if f (Seq.length list) then Just list else Nothing
  _SplitAt n
    = _LengthIs (>= n)
    . iso (Seq.splitAt n) (uncurry (<>))
    . crossPartialIso (_LengthIs (== max 0 n)) id
instance Streaming (Vector a) (Vector b) a b where
  _LengthIs f = partialIso lengthen lengthen where
    lengthen :: Vector c -> Maybe (Vector c)
    lengthen list = if f (Vector.length list) then Just list else Nothing
  _SplitAt n
    = _LengthIs (>= n)
    . iso (Vector.splitAt n) (uncurry (<>))
    . crossPartialIso (_LengthIs (== max 0 n)) id
instance (Storable a, Storable b)
  => Streaming (Storable.Vector a) (Storable.Vector b) a b where
  _LengthIs f = partialIso lengthen lengthen where
    lengthen :: Storable c => Storable.Vector c -> Maybe (Storable.Vector c)
    lengthen list = if f (Vector.length list) then Just list else Nothing
  _SplitAt n
    = _LengthIs (>= n)
    . iso (Vector.splitAt n) (uncurry (<>))
    . crossPartialIso (_LengthIs (== max 0 n)) id
instance (Unbox a, Unbox b)
  => Streaming (Unbox.Vector a) (Unbox.Vector b) a b where
  _LengthIs f = partialIso lengthen lengthen where
    lengthen :: Unbox c => Unbox.Vector c -> Maybe (Unbox.Vector c)
    lengthen list = if f (Vector.length list) then Just list else Nothing
  _SplitAt n
    = _LengthIs (>= n)
    . iso (Vector.splitAt n) (uncurry (<>))
    . crossPartialIso (_LengthIs (== max 0 n)) id
instance Streaming StrictB.ByteString StrictB.ByteString Word8 Word8 where
  _LengthIs f = partialIso lengthen lengthen where
    lengthen :: StrictB.ByteString -> Maybe StrictB.ByteString
    lengthen list = if f (StrictB.length list) then Just list else Nothing
  _SplitAt n
    = _LengthIs (>= n)
    . iso (StrictB.splitAt n) (uncurry (<>))
    . crossPartialIso (_LengthIs (== max 0 n)) id
instance Streaming LazyB.ByteString LazyB.ByteString Word8 Word8 where
  _LengthIs f = partialIso lengthen lengthen where
    lengthen :: LazyB.ByteString -> Maybe LazyB.ByteString
    lengthen list =
      if f (fromIntegral (LazyB.length list))
      then Just list else Nothing
  _SplitAt n
    = _LengthIs (>= n)
    . iso (LazyB.splitAt (fromIntegral n)) (uncurry (<>))
    . crossPartialIso (_LengthIs (== max 0 n)) id
instance Streaming StrictT.Text StrictT.Text Char Char where
  _LengthIs f = partialIso lengthen lengthen where
    lengthen :: StrictT.Text -> Maybe StrictT.Text
    lengthen list = if f (StrictT.length list) then Just list else Nothing
  _SplitAt n
    = _LengthIs (>= n)
    . iso (StrictT.splitAt n) (uncurry (<>))
    . crossPartialIso (_LengthIs (== max 0 n)) id
instance Streaming LazyT.Text LazyT.Text Char Char where
  _LengthIs f = partialIso lengthen lengthen where
    lengthen :: LazyT.Text -> Maybe LazyT.Text
    lengthen list =
      if f (fromIntegral (LazyT.length list))
      then Just list else Nothing
  _SplitAt n
    = _LengthIs (>= n)
    . iso (LazyT.splitAt (fromIntegral n)) (uncurry (<>))
    . crossPartialIso (_LengthIs (== max 0 n)) id

{- | `_HeadTail` `PartialIso` which decomposes a stream as
into a pair of its head and tail. -}
_HeadTail
  :: Stream s t a b
  => PartialIso s t (a,s) (b,t)
_HeadTail = _NotNull . _HeadTailMay . _Just

_NotNull
  :: (AsEmpty s, AsEmpty t)
  => PartialIso s t s t
_NotNull = partialIso notemp notemp where
  notemp s = if isn't _Empty s then Just s else Nothing

_Null
  :: (AsEmpty s, AsEmpty t)
  => PartialIso s t () ()
_Null = partialIso empA empB where
  empA s = if isn't _Empty s then Nothing else Just ()
  empB _ = Just Empty

{- | Bidirectional left fold/unfold with no empty case. -}
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

{- | Bidirectional right fold/unfold with no empty case. -}
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

{- | Bidirectional left fold/unfold with an empty case. -}
difoldl
  :: (Stream s t a b, Cons s t a b)
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

{- | A simple bidirectional left fold/unfold with an empty case. -}
difoldl'
  :: Stream' s a
  => APrism' (c,a) c
  -> Prism' (c,s) c
difoldl' i =
  let
    unit' = iso
      (\(a,()) -> a)
      (\a -> (a,()))
  in
    difoldl1 (clonePrism i)
    . aside _Empty
    . unit'

{- | Bidirectional right fold/unfold with an empty case. -}
difoldr
  :: (Stream s t a b, Cons s t a b)
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

{- | A simple bidirectional right fold/unfold with an empty case. -}
difoldr'
  :: Stream' s a
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
    . asideFst _Empty
    . unit'
