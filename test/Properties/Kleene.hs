{-# OPTIONS_GHC -Wno-orphans #-}
module Properties.Kleene (kleeneProperties) where

import Control.Lens.Grammar
import Data.Foldable (for_)
import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck

instance Arbitrary (TokenClass Char) where
  arbitrary = sized go
    where
      go 0 = frequency
        [ (1, pure falseP)
        , (1, pure trueP)
        , (4, oneOf <$> (arbitrary :: Gen [Char]))
        , (4, notOneOf <$> (arbitrary :: Gen [Char]))
        , (3, asIn <$> arbitrary)
        , (3, notAsIn <$> arbitrary)
        ]
      go n = frequency
        [ (2, go 0)
        , (2, (>|<) <$> go (n `div` 2) <*> go (n `div` 2))
        , (2, (>&&<) <$> go (n `div` 2) <*> go (n `div` 2))
        , (1, notP <$> go (n - 1))
        ]

instance Arbitrary (RegEx Char) where
  arbitrary = sized go
    where
      go 0 = frequency
        [ (1, pure (falseP :: RegEx Char))
        , (1, pure (mempty :: RegEx Char))
        , (6, tokenClass <$> (arbitrary :: Gen (TokenClass Char)))
        ]
      go n = frequency
        [ (2, go 0)
        , (2, (<>) <$> go (n `div` 2) <*> go (n `div` 2))
        , (2, (>|<) <$> go (n `div` 2) <*> go (n `div` 2))
        , (1, starK <$> go (n - 1))
        , (1, plusK <$> go (n - 1))
        , (1, optK <$> go (n - 1))
        ]

kleeneProperties :: Spec
kleeneProperties = do
  describe "KleeneStarAlgebra" $ do
    prop "starK x = optK (plusK x)" $ \(x :: RegEx Char) ->
      starK x == optK (plusK x)
    prop "plusK x = x <> starK x" $ \(x :: RegEx Char) ->
      plusK x == x <> starK x
    prop "optK x = mempty >|< x" $ \(x :: RegEx Char) ->
      optK x == (mempty >|< x)
    prop "x >|< x = x" $ \(x :: RegEx Char) ->
      (x >|< x) == x
    prop "falseP >|< x = x" $ \(x :: RegEx Char) ->
      (falseP >|< x) == x
    prop "x >|< falseP = x" $ \(x :: RegEx Char) ->
      (x >|< falseP) == x
    prop "x >|< mempty = optK x" $ \(x :: RegEx Char) ->
      (x >|< mempty) == optK x
    prop "falseP <> x = falseP" $ \(x :: RegEx Char) ->
      (falseP <> x) == falseP
    prop "x <> falseP = falseP" $ \(x :: RegEx Char) ->
      (x <> falseP) == falseP
    prop "mempty <> x = x" $ \(x :: RegEx Char) ->
      (mempty <> x) == x
    prop "x <> mempty = x" $ \(x :: RegEx Char) ->
      (x <> mempty) == x
  describe "TokenAlgebra" $ do
    it "falseP = tokenClass falseP" $
      (falseP :: RegEx Char) `shouldBe` tokenClass falseP
    prop "tokenClass x >|< tokenClass y = tokenClass (x >|< y)" $
      \(x :: TokenClass Char) (y :: TokenClass Char) ->
        ((tokenClass x :: RegEx Char) >|< tokenClass y)
          == tokenClass (x >|< y)
  describe "TokenAlgebra RegEx" $ do
    it "anyToken = tokenClass anyToken" $
      (anyToken :: RegEx Char) `shouldBe` tokenClass anyToken
    prop "token c = tokenClass (token c)" $
      \(c :: Char) ->
        (token c :: RegEx Char) == tokenClass (token c)
    prop "oneOf cs = tokenClass (oneOf cs)" $
      \(cs :: [Char]) ->
        (oneOf cs :: RegEx Char) == tokenClass (oneOf cs)
    prop "notOneOf cs = tokenClass (notOneOf cs)" $
      \(cs :: [Char]) ->
        (notOneOf cs :: RegEx Char) == tokenClass (notOneOf cs)
    prop "asIn cat = tokenClass (asIn cat)" $
      \(cat :: GeneralCategory) ->
        (asIn cat :: RegEx Char) == tokenClass (asIn cat)
    prop "notAsIn cat = tokenClass (notAsIn cat)" $
      \(cat :: GeneralCategory) ->
        (notAsIn cat :: RegEx Char) == tokenClass (notAsIn cat)
    it "matching agrees with lifted Bnf on examples" $ do
      let
        cases =
          [ ("", mempty :: RegEx Char)
          , ("a", token 'a')
          , ("b", token 'a')
          , ("ab", token 'a' <> token 'b')
          , ("a", token 'a' >|< token 'b')
          , ("bbb", starK (token 'b'))
          , ("bbb", plusK (token 'b'))
          , ("", optK (token 'b'))
          , ("x", oneOf "xyz")
          , ("x", notOneOf "abc")
          , ("A", asIn UppercaseLetter)
          , ("a", notAsIn UppercaseLetter)
          , ("abbb", token 'a' <> starK (token 'b'))
          , ("cat", terminal "cat" >|< terminal "dog")
          ]
      for_ cases $ \(word, rex) ->
        (word =~ rex) `shouldBe` (word =~ liftBnf0 rex)
  describe "BooleanAlgebra TokenClass" $ do
    it "trueP = anyToken" $
      (trueP :: TokenClass Char) `shouldBe` anyToken
    it "trueP = notOneOf []" $
      (trueP :: TokenClass Char) `shouldBe` notOneOf []
    it "falseP = oneOf []" $
      (falseP :: TokenClass Char) `shouldBe` oneOf []
    prop "notP . oneOf = notOneOf" $
      \(cs :: [Char]) ->
        notP (oneOf cs :: TokenClass Char) == notOneOf cs
    prop "notP . notOneOf = oneOf" $
      \(cs :: [Char]) ->
        notP (notOneOf cs :: TokenClass Char) == oneOf cs
    prop "notP . asIn = notAsIn" $
      \(cat :: GeneralCategory) ->
        notP (asIn cat :: TokenClass Char) == notAsIn cat
    prop "notP . notAsIn = asIn" $
      \(cat :: GeneralCategory) ->
        notP (notAsIn cat :: TokenClass Char) == asIn cat
    prop "x >|< x = x" $ \(x :: TokenClass Char) ->
      (x >|< x) == x
    prop "x >&&< x = x" $ \(x :: TokenClass Char) ->
      (x >&&< x) == x
