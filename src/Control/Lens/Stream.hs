module Control.Lens.Stream
  ( Nil (_Nil), nil, Null (_Null, _NotNull)
  , _Stream, _HeadTailMay, _HeadTail
  , SimpleStream (_All, _AllNot, _Span, _Break), convertStream
  , Stream (_LengthIs, _SplitAt)
  , difoldl1, difoldr1, difoldl, difoldr, difoldl'
  ) where

import Control.Lens
import Control.Lens.PartialIso

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
  :: (Null s t a b, Cons s t a b)
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
  :: (Nil s a, Cons s s a a)
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
  :: (Null s t a b, Cons s t a b)
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

class Nil s a | s -> a where
  _Nil :: Prism' s ()
instance Nil (Maybe a) a where
  _Nil = _Nothing
instance Nil [a] a where
  _Nil = prism (pure []) $ \case
    [] -> Right ()
    x -> Left x
instance Nil (Either () a) a where
  _Nil = _Left

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
instance Null [a] [b] a b where
  _Null = partialIso
    (\l -> if null l then Just () else Nothing)
    (pure (Just []))
  _NotNull = partialIso nonemp nonemp where
    nonemp l = if not (null l) then Just l else Nothing
instance Null (Either () a) (Either () b) a b where
  _Null = partialIso
    (either Just (pure Nothing))
    (pure (Just (Left ())))
  _NotNull = partialIso nonemp nonemp where
    nonemp (Left ()) = Nothing
    nonemp (Right x) = Just (Right x)

_Stream
  :: (Cons s s a a, Cons t t b b, Nil t b)
  => Iso s t (Either () (a,s)) (Either () (b,t))
_Stream = _HeadTailMay . _M2E

_HeadTailMay
  :: (Cons s s a a, Cons t t b b, Nil t b)
  => Iso s t (Maybe (a,s)) (Maybe (b,t))
_HeadTailMay = iso (preview _Cons) (maybe nil (uncurry cons))

_HeadTail
  :: (Null s t a b, Cons s s a a, Cons t t b b)
  => PartialIso s t (a,s) (b,t)
_HeadTail = _NotNull . _HeadTailMay . _Just

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
    . crossPartialIso (_LengthIs (== (max 0 n))) id

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

convertStream :: (SimpleStream s a, SimpleStream t a) => s -> t
convertStream s =
  either
    (const nil)
    (\(h,t) -> cons h (convertStream t))
    (view _Stream s)
