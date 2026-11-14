{-# LANGUAGE ExplicitNamespaces, RequiredTypeArguments #-}
module Properties.Nested (nestedProperties) where

import Control.Lens (preview, review, view)
import Control.Lens.Prism.Nested
import GHC.Generics (Generic)
import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck

data Shape
  = Dot
  | Circle Int
  | Rect Int Bool
  | Box Int Bool Char
  | Quad Int Bool Char Int
  deriving stock (Eq, Show, Generic)
makeNestedPrisms ''Shape

data Pt = Pt Int Bool Char
  deriving stock (Eq, Show, Generic)
makeNestedPrisms ''Pt

instance Arbitrary Shape where
  arbitrary = oneof
    [ pure Dot
    , Circle <$> arbitrary
    , Rect <$> arbitrary <*> arbitrary
    , Box <$> arbitrary <*> arbitrary <*> arbitrary
    , Quad <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
    ]

instance Arbitrary Pt where
  arbitrary = Pt <$> arbitrary <*> arbitrary <*> arbitrary

nestedProperties :: Spec
nestedProperties = do
  describe "genericNestedPrism, as makeNestedPrisms's prisms" $ do
    prop "previews as they do" $ \(s :: Shape) ->
      preview (genericNestedPrism Shape "Dot") s === preview _Dot s
        .&&. preview (genericNestedPrism Shape "Circle") s === preview _Circle s
        .&&. preview (genericNestedPrism Shape "Rect") s === preview _Rect s
        .&&. preview (genericNestedPrism Shape "Box") s === preview _Box s
        .&&. preview (genericNestedPrism Shape "Quad") s === preview _Quad s
    prop "reviews as they do" $ \n b c m ->
      review (genericNestedPrism Shape "Dot") () === review _Dot ()
        .&&. review (genericNestedPrism Shape "Circle") n === review _Circle n
        .&&. review (genericNestedPrism Shape "Rect") (n, b) === review _Rect (n, b)
        .&&. review (genericNestedPrism Shape "Box") (n, (b, c))
          === review _Box (n, (b, c))
        .&&. review (genericNestedPrism Shape "Quad") (n, (b, (c, m)))
          === review _Quad (n, (b, (c, m)))
  describe "genericNestedIso, as makeNestedPrisms's iso" $ do
    prop "views as it does" $ \(p :: Pt) ->
      view (genericNestedIso (type Pt)) p === view _Pt p
    prop "reviews as it does" $ \(n :: Int) b c ->
      review (genericNestedIso (type Pt)) (n, (b, c)) === review _Pt (n, (b, c))
