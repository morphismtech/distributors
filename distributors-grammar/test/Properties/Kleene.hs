{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Properties.Kleene (kleeneProperties) where

import Control.Lens.Grammar
import Data.Foldable (for_)
import Data.String (fromString)
import GHC.Exts (fromList, toList)
import Test.Hspec
import Test.Hspec.QuickCheck (modifyMaxSize, prop)
import Test.QuickCheck

#if !MIN_VERSION_QuickCheck(2,17,0)
import Data.Char (GeneralCategory)

-- | QuickCheck 2.17's instance, for earlier versions.
instance Arbitrary GeneralCategory where
  arbitrary = arbitraryBoundedEnum
  shrink = shrinkBoundedEnum
#endif

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
        , (2, (>&<) <$> go (n `div` 2) <*> go (n `div` 2))
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
  -- Small regular expressions, since `readG` backtracks exponentially.
  describe "Read & Show, as of strings" $ modifyMaxSize (const 8) $ do
    prop "read . show = id for RegString" $ \(x :: RegEx Char) ->
      let r = reparsed (RegString x) in read (show r) === r
    prop "reads a RegString within a list & a Maybe" $ \(x :: RegEx Char) ->
      let r = reparsed (RegString x)
      in read (show [r, r]) === [r, r] .&&. read (show (Just r)) === Just r
    prop "reads a RegString, leaving the rest" $ \(x :: RegEx Char) ->
      let r = reparsed (RegString x)
      in reads (show r <> " rest") === [(r, " rest")]
    it "read . show = id for RegBnf" $ do
      let bnf = fromString "{start} = \\q{a}|b*\n{a} = a" :: RegBnf
      read (show bnf) `shouldBe` bnf
      read (show [bnf]) `shouldBe` [bnf]
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
    prop "(x <> y) <> z = x <> (y <> z)" $ \(x :: RegEx Char) y z ->
      (x <> y) <> z === x <> (y <> z)
    prop "(x >|< y) >|< z = x >|< (y >|< z)" $ \(x :: RegEx Char) y z ->
      ((x >|< y) >|< z) === (x >|< (y >|< z))
    prop "TokenClass: (x >|< y) >|< z = x >|< (y >|< z)" $
      \(x :: TokenClass Char) y z ->
        ((x >|< y) >|< z) === (x >|< (y >|< z))
  describe "Prismoids act on KleeneStarAlgebras, by Grammor" $ do
    let grammor = Grammor :: RegEx Char -> Grammor (RegEx Char) Char Char
    prop "atLeast 1 >?* Grammor x = Grammor (plusK x)" $ \(x :: RegEx Char) ->
      runGrammor (atLeast 1 >?* grammor x) == plusK x
    prop "several >?* Grammor x = Grammor (starK x)" $ \(x :: RegEx Char) ->
      runGrammor (several >?* grammor x) == starK x
    prop "opted def >?* Grammor x = Grammor (optK x)" $ \(x :: RegEx Char) ->
      runGrammor (opted (only 'a') >?* grammor x) == optK x
  describe "manyTillP & sepBy at Grammor" $ do
    prop "sepBy sep (several . several) is finite at Grammor" $ \(x :: RegEx Char) ->
      let sep = Grammor (token ',') :: Grammor (RegEx Char) () ()
          r = runGrammor (sepBy sep (several . several) (Grammor x :: Grammor (RegEx Char) Char Char))
      in r == r
    prop "skippedMany >?* x = starK x, by Grammor" $ \(x :: RegEx Char) ->
      runGrammor (skippedMany >?* (Grammor x :: Grammor (RegEx Char) Char Char) :: Grammor (RegEx Char) () ())
        == starK x
    prop "manyTillP x y = starK x <> y, by Grammor" $ \(x :: RegEx Char) y ->
      runGrammor (manyTillP (Grammor x) (Grammor y) :: Grammor (RegEx Char) [()] [()])
        == starK x <> y
  describe "Counted Prismoids & skippedOptional print & parse, by Printor & Parsor" $
    modifyMaxSize (const 8) $ do
      let
        printed :: Prismoid String String Char Char -> String -> Maybe String
        printed pat s = ($ "") <$> printP (pat >?* (anyToken :: Printor String Maybe Char Char)) s
        parsed :: Prismoid String String Char Char -> String -> Maybe (String, String)
        parsed pat s = parseP (pat >?* (anyToken :: Parsor String Maybe Char Char)) s
        bounded lo hi s = lo <= length s && length s <= hi
      prop "inRange lo hi prints & parses exactly lo to hi tokens" $
        \(s :: String) -> forAll (choose (0, 4)) $ \lo -> forAll (choose (0, 4)) $ \hi ->
          printed (inRange lo (Just hi)) s === (if bounded lo hi s then Just s else Nothing)
            .&&. (if bounded lo hi s then parsed (inRange lo (Just hi)) s === Just (s, "") else property True)
      prop "atMost n prints & parses at most n tokens" $
        \(s :: String) -> forAll (choose (0, 4)) $ \n ->
          printed (atMost n) s === (if length s <= n then Just s else Nothing)
            .&&. parsed (atMost n) s === Just (splitAt n s)
      prop "atLeast n prints & parses at least n tokens" $
        \(s :: String) -> forAll (choose (0, 4)) $ \n ->
          printed (atLeast n) s === (if length s >= n then Just s else Nothing)
            .&&. parsed (atLeast n) s === (if length s >= n then Just (s, "") else Nothing)
      it "skippedOptional prints nothing, & parses one or none" $ do
        let comma = token ',' :: Printor String Maybe Char Char
            comma' = token ',' :: Parsor String Maybe Char Char
        (($ "") <$> printP (skippedOptional >?* comma) ()) `shouldBe` Just ""
        parseP (skippedOptional >?* comma') "," `shouldBe` Just ((), "")
        parseP (skippedOptional >?* comma') "" `shouldBe` Just ((), "")
        parseP (skippedOptional >?* comma') "x" `shouldBe` Just ((), "x")
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
    prop "x >&< x = x" $ \(x :: TokenClass Char) ->
      (x >&< x) == x

-- | A `RegString` as its printed text parses, which `read` reads.
reparsed :: RegString -> RegString
reparsed = fromList . toList


