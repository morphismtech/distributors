module Properties.Decoding (decodingProperties) where

import Control.Lens.Grammar
import Control.Lens.Grammar.Decoding
import Control.Monad (forM_)
import Control.Monad.State (evalState, State)
import Data.Either (isRight)
import Data.Functor.Identity (Identity (..))
import qualified Data.IntMap.Strict as IntMap
import Data.List (inits, nub)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Maybe (isJust)
import System.Random (StdGen, mkStdGen)
import Test.Hspec
import Test.Hspec.QuickCheck (modifyMaxSuccess, prop)
import Test.QuickCheck (choose, conjoin, counterexample, forAll, (===))
import qualified Test.QuickCheck as QC

import Examples.Arithmetic
import Examples.Json
import Examples.Lambda
import Examples.SemVer
import Examples.SExpr
import Examples.Vocabulary

-- | A grammar under test, with words of its language, from which
-- an alphabet & a vocabulary are drawn, & how many times to test
-- properties which parse, as some grammars parse slowly: parseG
-- builds the JSON example's class of over a million tokens each run.
data Subject = forall a. Subject String (Grammar Char a) [String] Int

subjects :: [Subject]
subjects =
  [ Subject "json" jsonGrammar (map snd jsonExamples) 20
  , Subject "arith" arithGrammar (map snd arithExamples) 100
  , Subject "semver" semverGrammar (map snd semverExamples) 100
  , Subject "sexpr" sexprGrammar (map snd sexprExamples) 100
  , Subject "lambda" lambdaGrammar (map snd lambdaExamples) 100
  , Subject "regex" regexGrammar (map snd regexExamples') 100
  ]
  where
    regexExamples' = [((), s) | s <- ["a|b", "(ab)*c", "[a-z]+", "x?y"]]

alphabetOf :: [String] -> String
alphabetOf ws = nub (concat ws <> " ;#")

parses :: Grammar Char a -> String -> Bool
parses grammar w = not (null [() | (_, "") <- parseG grammar w])

decodingProperties :: Spec
decodingProperties = do
  forM_ subjects $ \(Subject name grammar examples parsings) -> describe name $ do
    let
      parsing = modifyMaxSuccess (const parsings)
      et = transducerG grammar
      alphabet = alphabetOf examples
      pieces = vocabularyOf examples
      vocab = vocabulary pieces
      -- words of the language, & strings of its alphabet, mostly not
      wordsG = QC.elements examples
      stringsG = QC.listOf (QC.elements alphabet)
      candidatesG = QC.oneof [wordsG, stringsG, mutate =<< wordsG]
      mutate w = do
        i <- choose (0, length w)
        c <- QC.elements alphabet
        pure (take i w <> [c] <> drop (i + 1) w)

    parsing $ prop "a chart accepts the words parseG fully parses" $
      forAll candidatesG $ \w ->
        maybe False chartAccepts (scanChartMany w (startChart et)) === parses grammar w

    prop "a chart expects exactly the tokens it scans" $
      forAll wordsG $ \w -> conjoin
        [ counterexample (show (prefix, x)) $
            tokenClass (chartExpects chart) x === isJust (scanChart x chart)
        | prefix <- inits w
        , Just chart <- [scanChartMany prefix (startChart et)]
        , x <- alphabet
        ]

    prop "expectNext agrees with an incrementally scanned chart" $
      forAll candidatesG $ \w ->
        expectNext et w
          === maybe falseP chartExpects (scanChartMany w (startChart et))

    prop "allowedPieces are the pieces a chart scans whole" $
      forAll wordsG $ \w -> conjoin
        [ counterexample (show prefix) $
            IntMap.keys (allowedPieces vocab chart)
              === [ i | (i, piece) <- zip [0 ..] pieces
                      , isJust (scanChartMany piece chart) ]
        | prefix <- inits w
        , Just chart <- [scanChartMany prefix (startChart et)]
        ]

    parsing $ prop "sampling finishes at words of the language, & truncates at their prefixes" $
      \seed -> forAll (choose (1, 60)) $ \bound ->
        let
          predictor = randomPredictor 0.2 seed (length pieces)
          decoded = evalState (decode sampled (lift' predictor) vocab bound et) (mkStdGen seed)
        in counterexample (show decoded) $ case decoded of
          Finished w -> parses grammar w
          Truncated w -> isJust (scanChartMany w (startChart et))
          Stuck w -> isJust (scanChartMany w (startChart et))

    prop "decoding by positive weights is stuck only where no piece is allowed" $
      \seed -> forAll (choose (1, 60)) $ \bound ->
        let
          predictor = randomPredictor 0 seed (length pieces)
          decoded = evalState (decode sampled (lift' predictor) vocab bound et) (mkStdGen seed)
        in counterexample (show decoded) $ case decoded of
          Stuck w -> case scanChartMany w (startChart et) of
            Just chart -> IntMap.null (allowedPieces vocab chart) && not (chartAccepts chart)
            Nothing -> False
          _ -> True

    prop "greedy decoding with opportunistic masking is decoding with a mask every step" $
      \seed -> forAll (choose (1, 60)) $ \bound ->
        let predictor = randomPredictor 0.2 seed (length pieces)
        in runIdentity (decode greedy predictor vocab bound et)
             === runIdentity (maskedDecode greedy predictor vocab bound et)

    parsing $ prop "decodeG parses exactly when decoding finishes" $
      \seed -> forAll (choose (1, 60)) $ \bound ->
        let
          predictor = randomPredictor 0.2 seed (length pieces)
          decoded = runIdentity (decode greedy predictor vocab bound et)
          typed = runIdentity (decodeG greedy predictor vocab bound grammar)
        in isRight typed === isFinished decoded

  describe "sampling with opportunistic masking" $
    it "samples as masking every step does" $ do
      let
        et = transducerG @Char smallG
        vocab = vocabulary smallPieces
        predictor = randomPredictor 0.2 11 (length smallPieces)
        runs = 6000 :: Int
        empirical = frequencies
          [ evalState (decode sampled (lift' predictor) vocab 20 et) (mkStdGen seed)
          | seed <- [1 .. runs] ]
        exact = maskedProbabilities predictor vocab 20 et
      forM_ (Map.toList exact) $ \(decoded, p) ->
        Map.findWithDefault 0 decoded empirical `shouldSatisfy` (\q -> abs (q - p) < 0.03)
      Map.keysSet empirical `shouldSatisfy` (`all'` (`Map.member` exact))
  where
    lift' :: Predictor Identity -> Predictor (State StdGen)
    lift' predictor = pure . runIdentity . predictor
    isFinished = \case
      Finished _ -> True
      _ -> False
    all' xs p = all p xs

-- | A small language, with words which share prefixes, & pieces
-- which cross its words' parts.
smallG :: Grammar Char ()
smallG = orP [terminal "true", terminal "truth", terminal "false", terminal "fa"]

smallPieces :: [String]
smallPieces = ["t", "r", "u", "e", "h", "f", "a", "l", "s", "tr", "ue", "true", "th", "fa", "lse", "false"]

frequencies :: Ord a => [a] -> Map a Double
frequencies xs = Map.map (/ fromIntegral (length xs)) (Map.fromListWith (+) [(x, 1) | x <- xs])

-- | The exact distribution of decoding by sampling from masked weights
-- every step, by enumerating every choice.
maskedProbabilities
  :: Predictor Identity -> Vocabulary Char -> Int -> Transducer Char
  -> Map (Decoded Char) Double
maskedProbabilities predict vocab bound et =
  Map.fromListWith (+) (go 0 [] [] (startChart et) 1)
  where
    go n pieces chunks chart p
      | n >= bound = [(Truncated text, p)]
      | total <= 0 = [(Stuck text, p)]
      | otherwise =
          [(Finished text, p * end / total) | end > 0]
          <> concat
            [ go (n + 1) (i : pieces) (piece : chunks) chart' (p * w / total)
            | (i, w) <- IntMap.toList ws
            , Just chart' <- [IntMap.lookup i allowed]
            , Just piece <- [vocabularyPiece vocab i]
            ]
      where
        text = concat (reverse chunks)
        weights = runIdentity (predict (reverse pieces))
        allowed = allowedPieces vocab chart
        ws = IntMap.filter (> 0) (IntMap.intersectionWith const (pieceWeights weights) allowed)
        end = if chartAccepts chart then max 0 (endWeight weights) else 0
        total = end + sum ws
