module Main (main) where

import Data.IORef
import Data.Profunctor.Monoidal (meander)
import Data.Profunctor.Types (Star (..))
import Test.Hspec

import Properties.Homogeneous
import Properties.Nested
import Properties.PartialIso
import Properties.Parsing

main :: IO ()
main = hspec $ do
  describe "Homogeneous" homogeneousProperties
  describe "PartialIso" partialIsoProperties
  describe "Nested" nestedProperties
  describe "Parsing" parsingProperties
  describe "meander" meanderProperties

meanderProperties :: Spec
meanderProperties =
  it "preserves left-to-right traversal effects" $ do
    let input = ["h", "e", "l", "l", "o"]
    seenRef <- newIORef []
    let visit item = modifyIORef' seenRef (item :) >> pure ()
    units <- runStar (meander traverse (Star visit)) input
    seen <- reverse <$> readIORef seenRef
    seen `shouldBe` input
    units `shouldBe` replicate (length input) ()
