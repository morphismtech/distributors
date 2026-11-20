module Properties.PartialIso (partialIsoProperties) where

import Control.Lens (over, preview, review, traverseOf, view)
import Control.Lens.PartialIso
import Data.Profunctor (Cochoice (..), Forget (..))
import Data.Profunctor.Filtrator (Filtrator (..))
import Data.Monoid.Disjunctive
import Test.Hspec
import Witherable (catMaybes)
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck

partialIsoProperties :: Spec
partialIsoProperties = do
  checkPartialIso "partialIso" halve
  checkTraverse "partialIso" halve
  checkPartialIso "partialIso, composed" (halve . halve)
  checkTraverse "partialIso, composed" (halve . halve)
  checkPartialIso "satisfied" (satisfied (even :: Int -> Bool))
  checkTraverse "satisfied" (satisfied (even :: Int -> Bool))
  checkPartialIso "nulled" (nulled :: PartialIso' [Int] ())
  checkTraverse "nulled" (nulled :: PartialIso' [Int] ())
  checkPartialIso "notNulled" (notNulled :: PartialIso' [Int] [Int])
  checkTraverse "notNulled" (notNulled :: PartialIso' [Int] [Int])
  checkPartialIso "filterPrism" (filterPrism _Just :: PartialIso' Int (Maybe Int))
  checkTraverse "filterPrism" (filterPrism _Just :: PartialIso' Int (Maybe Int))
  describe "filterPrism" $ do
    prop "reverses a Prism, forwards by view as it reviews" $ \(x :: Int) ->
      view (filterPrism _Just) x === review _Just x
    prop "reverses a Prism, backwards by preview as it previews" $
      \(m :: Maybe Int) ->
        preview (coPartialIso (filterPrism _Just)) m === preview _Just m
  checkPartialIso "a Prism" (_Just :: PartialIso' (Maybe Int) Int)
  describe "a Prism" $
    prop "traverseOf passes a mismatch through, as its clone does, unlike its partial functions" $
      \(Fun _ f :: Fun Int (Maybe Int)) -> within second $
        traverseOf _Just f Nothing === Just Nothing
          .&&. traverseOf (clonePartialIso _Just) f Nothing === Just Nothing
          .&&. traverseOf (withPartialIso _Just partialIso) f Nothing === Nothing
  describe "PartialMarket, isomorphic to PartialIso" $ do
    prop "partialMarket . withPartialMarket keeps a Prism's passing through" $
      \(Fun _ f :: Fun Int (Maybe Int)) (m :: Maybe Int) -> within second $
        traverseOf (remarket _Just) f m
          === traverseOf _Just f m
    prop "partialMarket . withPartialMarket keeps a PartialIso" $
      \(Fun _ f :: Fun Int (Maybe Int)) (n :: Int) -> within second $
        traverseOf (remarket halve) f n
          === traverseOf halve f n
    prop "withPartialMarket . partialMarket is the identity" $
      \(n :: Int) (b :: Int) -> within second $
        let build x = if x > 0 then Just (x * 2) else Nothing
            match x
              | even x = Right (x `div` 2)
              | x > 0 = Left (Just x)
              | otherwise = Left Nothing
        in withPartialMarket (partialMarket build match) (\build' match' -> (build' b, match' n))
          === (build b, match n)
    prop "is a filterPrism after a Prism" $
      \(Fun _ f :: Fun Int (Maybe Int)) (n :: Int) -> within second $
        let build x = if x > 0 then Just (x * 2) else Nothing
            match x
              | even x = Right (x `div` 2)
              | x > 0 = Left (Just x)
              | otherwise = Left Nothing
        in traverseOf (partialMarket build match) f n
          === traverseOf (filterPrism _Just . prism build (maybe (Left Nothing) match)) f n
    prop "forgetting passing through gives its partial functions" $
      \(m :: Maybe Int) (b :: Int) -> within second $
        withPartialMarket _Just (\build match -> (either (const Nothing) Just (match m), build b))
          === withPartialIso _Just (\match' build' -> (match' m, build' b))
  describe "combinators keep passing through" $ do
    prop "withoutPartialIso of Prisms is their sum" $
      \(Fun _ f :: Fun Int (Maybe Int)) (e :: Either (Maybe Int) (Maybe Int)) -> within second $
        traverseOf (withoutPartialIso _Just _Just) (either (fmap Left . f) (fmap Right . f)) e
          === either (fmap Left . traverseOf _Just f) (fmap Right . traverseOf _Just f) e
    prop "alongsidePartialIso of Prisms passes through where both do" $
      \(Fun _ f :: Fun (Int, Int) (Maybe (Int, Int))) (m :: Maybe Int) (n :: Maybe Int) -> within second $
        traverseOf (alongsidePartialIso _Just _Just) f (m, n)
          === case (m, n) of
            (Just x, Just y) -> f (x, y) >>= \(x', y') -> Just (Just x', Just y')
            (Nothing, Nothing) -> Just (Nothing, Nothing)
            _ -> Nothing
    prop "orPartialIso is the union of patterns" $
      \(n :: Int) -> within second $
        traverseOf (orPartialIso (satisfied even) (satisfied odd)) Just n === Just n
    prop "falsePartialIso is orPartialIso's identity" $
      \(Fun _ f :: Fun Int (Maybe Int)) (m :: Maybe Int) -> within second $
        traverseOf (orPartialIso falsePartialIso _Just) f m === traverseOf _Just f m
          .&&. traverseOf (orPartialIso _Just falsePartialIso) f m === traverseOf _Just f m
    prop "coPartialIso twice rebuilds from partial functions" $
      \(Fun _ f :: Fun Int (Maybe Int)) (m :: Maybe Int) -> within second $
        traverseOf (coPartialIso (coPartialIso _Just)) f m
          === traverseOf (withPartialIso _Just partialIso) f m
  describe "a PartialIso is a Prism with a Maybe target" $ do
    prop "withPrism . withPartialMarket keeps a PartialIso" $
      \(Fun _ f :: Fun Int (Maybe Int)) (n :: Int) (m :: Maybe Int) -> within second $
        let viaPrism :: APartialIso s t Int Int -> PartialIso s t Int Int
            viaPrism pattern = withPrism (withPartialMarket pattern prism) partialMarket
        in traverseOf (viaPrism halve) f n === traverseOf halve f n
          .&&. traverseOf (viaPrism _Just) f m === traverseOf _Just f m
    prop "withPartialMarket . withPrism keeps a Prism" $
      \(Fun _ f :: Fun Int Int) (n :: Int) -> within second $
        let prsm :: Prism Int (Maybe Int) Int Int
            prsm = withPartialMarket halve prism
        in over (withPartialMarket (withPrism prsm partialMarket) prism) f n === over prsm f n
  describe ">?< passes through as >? does" $ do
    prop "prsm >?< p = prsm >? p, at (->)" $
      \(Fun _ f :: Fun Int Int) (m :: Maybe Int) (e :: Either Int Char) -> within second $
        (_Just >?< f) m === (_Just >? f) m
          .&&. (_Left >?< f) e === (_Left >? f) e
    prop "withPrism prsm partialMarket >?< p = catMaybes (prsm >? p), at PartialMarket" $
      \(m0 :: Market') (b :: Int) (n :: Int) (m :: Maybe Int) -> within second $
        let halves :: Prism Int (Maybe Int) Int Int
            halves = withPartialMarket halve prism
            justs :: Prism (Maybe Int) (Maybe (Maybe Int)) Int Int
            justs = withPartialMarket _Just prism
        in observe (withPrism halves partialMarket >?< market m0) b n
            === observe (catMaybes (halves >? market m0)) b n
          .&&. observe (withPrism justs partialMarket >?< market m0) b m
            === observe (catMaybes (justs >? market m0)) b m
    prop "partialIso match build >?< p = dimapMaybe match build p, at Forget" $
      \(n :: Int) -> within second $
        let match, build :: Int -> Maybe Int
            match k = if even k then Just (k `div` 2) else Nothing
            build k = Just (k * 2)
        in runForget (partialIso match build >?< Forget (: [])) n
          === runForget (dimapMaybe match build (Forget (: []))) n
  describe "PartialMarket's instances are lawful" $ do
    prop "unleft . left' = id" $
      \(Fun _ build :: Fun Int (Maybe Int)) (Fun _ match :: Fun Int (Either (Maybe Int) Int)) x y ->
        observe (unleft (left' (PartialMarket build match :: PartialMarket Int Int Int Int))) x y
          === observe (PartialMarket build match) x y
    prop "unright . right' = id" $
      \(Fun _ build :: Fun Int (Maybe Int)) (Fun _ match :: Fun Int (Either (Maybe Int) Int)) x y ->
        observe (unright (right' (PartialMarket build match :: PartialMarket Int Int Int Int))) x y
          === observe (PartialMarket build match) x y
    prop "fst . filtrate = unleft, snd . filtrate = unright" $
      \(Fun _ build :: Fun Int (Maybe (Either Int Int))) (Fun _ match :: Fun (Either Int Int) (Either (Maybe (Either Int Int)) Int)) x y ->
        let sums = PartialMarket build match :: PartialMarket Int Int (Either Int Int) (Either Int Int)
        in observe (fst (filtrate sums)) x y === observe (unleft sums) x y
          .&&. observe (snd (filtrate sums)) x y === observe (unright sums) x y
    prop ">|< is associative" $
      \(m0 :: Market') m1 m2 x y ->
        observe (market m0 >|< (market m1 >|< market m2)) x y
          === observe ((market m0 >|< market m1) >|< market m2) x y
    prop "falseP is its identity" $
      \(m0 :: Market') x y ->
        observe (falseP >|< market m0) x y === observe (market m0) x y
          .&&. observe (market m0 >|< falseP) x y === observe (market m0) x y
  describe "satisfied, a homomorphism of predicates" $ do
    prop "from >|< to >|< of partial functions" $
      \(Fun _ p :: Fun Int Bool) (Fun _ q) x y ->
        exchanged (satisfied (p >|< q)) x y
          === exchanging
            ( withPartialIso (satisfied p) (,)
              >|< withPartialIso (satisfied q) (,) ) x y
    prop "from falseP to falseP" $ \x y ->
      exchanged (satisfied (falseP :: Int -> Bool)) x y
        === exchanging falseP x y
    prop "from >&< to composition" $
      \(Fun _ p :: Fun Int Bool) (Fun _ q) x y ->
        exchanged (satisfied (p >&< q)) x y
          === exchanged (satisfied p . satisfied q) x y
  where
    remarket :: APartialIso s t a b -> PartialIso s t a b
    remarket pattern = withPartialMarket pattern partialMarket
    exchanged :: APartialIso s t a b -> s -> b -> (Maybe a, Maybe t)
    exchanged pattern = exchanging (withPartialIso pattern (,))
    exchanging :: (s -> Maybe a, b -> Maybe t) -> s -> b -> (Maybe a, Maybe t)
    exchanging (match, build) s b = (match s, build b)

type Market' = (Fun Int (Maybe Int), Fun Int (Either (Maybe Int) Int))

market :: Market' -> PartialMarket Int Int Int Int
market (Fun _ build, Fun _ match) = PartialMarket build match

observe :: PartialMarket a b s t -> b -> s -> (Maybe t, Either (Maybe t) a)
observe (PartialMarket build match) b s = (build b, match s)

halve :: PartialIso' Int Int
halve = partialIso
  (\n -> if even n then Just (n `div` 2) else Nothing)
  (Just . (* 2))

{- | The combinators which run a `PartialIso`
agree with the partial functions which characterize it,
& terminate, failing or not.
-}
checkPartialIso
  :: (Arbitrary s, Show s, Eq s, Arbitrary a, Show a, Eq a)
  => String -> PartialIso' s a -> Spec
checkPartialIso name pattern = describe name $ do
  prop "preview matches forwards" $ \s -> within second $
    preview pattern s === withPartialIso pattern const s
  prop "preview of coPartialIso builds backwards" $ \a -> within second $
    preview (coPartialIso pattern) a === withPartialIso pattern (const id) a
  prop "clonePartialIso keeps both directions" $ \s a -> within second $
    withPartialIso (clonePartialIso pattern) (\match build -> (match s, build a))
      === withPartialIso pattern (\match build -> (match s, build a))

{- | A `PartialIso` which fails by `Filterable`, like those `partialIso`
builds, traverses by matching, then building, failing if either does.
-}
checkTraverse
  :: (Arbitrary s, Show s, Eq s)
  => String -> PartialIso' s a -> Spec
checkTraverse name pattern = describe name $
  prop "traverseOf with Just matches, then builds" $ \s -> within second $
    traverseOf pattern Just s
      === withPartialIso pattern (\match build -> build =<< match s)

second :: Int
second = 1000000
