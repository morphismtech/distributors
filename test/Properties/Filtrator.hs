module Properties.Filtrator
  ( filtratorSpec
  ) where

import Control.Lens.Grammar
import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck

{- | The laws relating `filtrate` & `>+<`,

prop> filtrate (x >+< y) = (x, y)
prop> uncurry (>+<) (filtrate r) = r

observed by printing & parsing, up to failure messages.
They hold for printers & backtracking parsers, but not for predictive
parsers, which commit once they consume, since a projection of `filtrate`
consumes before it rejects the other summand.
-}
filtratorSpec :: Spec
filtratorSpec = describe "Filtrator" $ do
  describe "filtrate (x >+< y) = (x, y)" $ do
    prop "prints, by Printor" $ \c ->
      printed (fst (filtrate (ab >+< bc))) c === printed ab c
      .&&. printed (snd (filtrate (ab >+< bc))) c === printed bc c
    prop "prints predictively, by Parsector" $ \c ->
      unparsec (fst (filtrate (ab >+< bc))) c === unparsec ab c
      .&&. unparsec (snd (filtrate (ab >+< bc))) c === unparsec bc c
    prop "parses by backtracking, by Parsor" $ forAll input $ \str ->
      parsed (fst (filtrate (ab >+< bc))) str === parsed ab str
      .&&. parsed (snd (filtrate (ab >+< bc))) str === parsed bc str
    prop "parses predictively, by Parsector, successes of disjoint summands" $
      forAll input $ \str ->
        succeeded (fst (filtrate (ab >+< cd))) str === succeeded ab str
        .&&. succeeded (snd (filtrate (ab >+< cd))) str === succeeded cd str
    it "doesn't parse predictively a failure, by Parsector, consuming it" $
      parsec (fst (filtrate (ab >+< cd))) "c" `shouldNotBe` parsec ab "c"
    it "doesn't parse predictively overlapping summands, by Parsector" $
      parsec (snd (filtrate (ab >+< bc))) "b"
        `shouldNotBe` parsec bc "b"
  describe "uncurry (>+<) (filtrate r) = r" $ do
    prop "prints, by Printor" $ \e ->
      printed (uncurry (>+<) (filtrate consuming)) e === printed consuming e
    prop "prints predictively, by Parsector" $ \e ->
      unparsec (uncurry (>+<) (filtrate consuming)) e
        === unparsec consuming e
    prop "parses by backtracking, by Parsor" $ forAll input $ \str ->
      parsed (uncurry (>+<) (filtrate consuming)) str === parsed consuming str
    it "doesn't parse predictively, by Parsector, committing to a projection" $
      parsec (uncurry (>+<) (filtrate (ab >+< cd))) "d"
        `shouldNotBe` parsec (ab >+< cd) "d"
  where
    ab, bc, cd :: Grammar Char Char
    ab = oneOf "ab"
    bc = oneOf "bc"
    cd = oneOf "cd"
    -- a sum which consumes a token before choosing its summand
    consuming :: Grammar Char (Either Char Char)
    consuming = terminal "<" >* (ab >+< cd)
    input = do
      n <- choose (0, 3)
      vectorOf n (elements "<abcd")

printed :: Printor String Maybe a b -> a -> Maybe String
printed p a = ($ "") <$> printP p a

unparsec :: Parsector String a b -> a -> (Maybe b, String)
unparsec p a = let st = unparsecP p a "" in (parsecResult st, parsecStream st)

parsed :: Parsor String [] a b -> String -> [(b, String)]
parsed = parseP

-- | A predictive parse, if it succeeds.
succeeded :: Parsector String a b -> String -> Maybe (b, String)
succeeded p str = case parsec p str of
  (Just b, rest) -> Just (b, rest)
  (Nothing, _) -> Nothing

parsec :: Parsector String a b -> String -> (Maybe b, String)
parsec p str = let st = parsecP p str in (parsecResult st, parsecStream st)
