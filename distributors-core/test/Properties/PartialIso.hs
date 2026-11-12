module Properties.PartialIso (partialIsoProperties) where

import Control.Lens (preview, traverseOf)
import Control.Lens.PartialIso
import Test.Hspec
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
  checkPartialIso "a coPrism" (coPrism _Just :: PartialIso' Int (Maybe Int))
  checkTraverse "a coPrism" (coPrism _Just :: PartialIso' Int (Maybe Int))
  checkPartialIso "a Prism" (_Just :: PartialIso' (Maybe Int) Int)
  describe "a Prism" $
    prop "traverseOf passes a mismatch through, unlike its clone" $
      \(Fun _ f :: Fun Int (Maybe Int)) -> within second $
        traverseOf _Just f Nothing === Just Nothing
          .&&. traverseOf (clonePartialIso _Just) f Nothing === Nothing

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
