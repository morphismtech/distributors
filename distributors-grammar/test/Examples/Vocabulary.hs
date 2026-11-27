-- | Vocabularies & predictors, to decode the example grammars by,
-- & a reference decoder which masks its predictor every step.
module Examples.Vocabulary
  ( vocabularyOf
  , randomPredictor
  , maskedDecode
  ) where

import Control.Lens.Grammar
import Control.Lens.Grammar.Decoding
import Data.Functor.Identity (Identity (..))
import qualified Data.IntMap.Strict as IntMap
import Data.List (nub, tails)
import System.Random (mkStdGen, randoms)

-- | A vocabulary of pieces like a sub-word tokenizer's: every token
-- of some words, & a few more, & the substrings of the words of
-- two to five tokens, with some junk.
vocabularyOf :: [String] -> [String]
vocabularyOf ws = nub $
  map pure (nub (concat ws <> " ;#"))
  <> [ piece | w <- ws, t <- tails w, n <- [2 .. 5], let piece = take n t, length piece == n ]
  <> ["#junk", ";;", "  "]

-- | A deterministic predictor over a vocabulary of a given size, which
-- weighs pieces pseudo-randomly, by a seed & the pieces so far,
-- with a given share of the weights zero.
randomPredictor :: Double -> Int -> Int -> Predictor Identity
randomPredictor zeros seed size pieces = Identity (Weights weights end)
  where
    gen = mkStdGen (foldl (\h i -> h * 1000003 + i + 1) seed pieces)
    draws = take (size + 1) (randoms gen :: [Double])
    weights = IntMap.fromList
      [ (i, if d < zeros then 0 else d) | (i, d) <- zip [0 .. size - 1] draws ]
    end = last draws

-- | Decoding which masks every step, the reference `decode` is
-- tested against, & benchmarked against.
maskedDecode
  :: Monad m
  => Chooser m -> Predictor m -> Vocabulary Char -> Int
  -> Transducer Char -> m (Decoded Char)
maskedDecode chooser predict vocab bound et = go 0 [] [] (startChart et)
  where
    go n pieces chunks chart
      | n >= bound = pure (Truncated text)
      | otherwise = do
          weights <- predict (reverse pieces)
          let
            allowed = allowedPieces vocab chart
            masked = Weights
              (IntMap.filter (> 0) (IntMap.intersectionWith const (pieceWeights weights) allowed))
              (if chartAccepts chart then max 0 (endWeight weights) else 0)
          if IntMap.null (pieceWeights masked) && endWeight masked <= 0
            then pure (Stuck text)
            else chooser masked >>= \case
              Nothing -> pure (Finished text)
              Just i -> case (IntMap.lookup i allowed, vocabularyPiece vocab i) of
                (Just chart', Just piece) -> go (n + 1) (i : pieces) (piece : chunks) chart'
                _ -> pure (Stuck text)
      where
        text = concat (reverse chunks)
