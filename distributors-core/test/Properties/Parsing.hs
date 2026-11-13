module Properties.Parsing (parsingProperties) where

import Control.Lens.Diopter (several, skippedOptional)
import Control.Lens.Monocle (ditraversed)
import Control.Lens.Prismoid
import Control.Monad.Trans.State (StateT (..))
import Data.Bifunctor.Joker (Joker (..))
import Data.Char (isDigit)
import Data.Functor.Identity (Identity (..))
import Data.Functor.Product (Product (..))
import Data.List (intercalate)
import Control.Lens (Prism', prism')
import Data.Profunctor (rmap)
import Data.Profunctor.Distributor (Alternator (..))
import Data.Profunctor.Monoidal ((>*), (*<), replicateP)
import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck
import Text.ParserCombinators.ReadP (ReadP, char, readP_to_S, satisfy)

parsingProperties :: Spec
parsingProperties = do
  describe "sepBy" $ do
    prop "sepBy sep several parses exactly the separated digits" $
      \(Digits ds) -> parses (rmap Identity (inBrackets (sepBy comma several plainDigit))) (bracketed ds)
        === [ds]
    prop "sepBy sep (atLeast 1) parses exactly some separated digits" $
      \(Digits ds) -> parses (rmap Identity (inBrackets (sepBy comma (atLeast 1) plainDigit))) (bracketed ds)
        === [ds | not (null ds)]
    prop "sepBy sep (exactly n) parses exactly n separated digits" $
      \(Digits ds) (Small k) -> let n = length ds in
        parses (rmap Identity (inBrackets (sepBy comma (exactly n) plainDigit) :: Joker ReadP String String)) (bracketed ds)
          === [ds]
        .&&. parses (rmap Identity (inBrackets (sepBy comma (exactly (n + 1 + abs k)) plainDigit) :: Joker ReadP String String)) (bracketed ds)
          === []
    prop "sepBy sep (chain1 assoc pat) associates, left or right" $
      \(Digits ds) -> let str = bracketed ds; leaves = map Leaf ds in
        parses (rmap Identity (inBrackets (sepBy comma (chain1 Left _Node) plainLeaf))) str
          === [foldl1 Node leaves | not (null ds)]
        .&&. parses (rmap Identity (inBrackets (sepBy comma (chain1 Right _Node) plainLeaf))) str
          === [foldr1 Node leaves | not (null ds)]
    prop "sepBy sequences greedily, deterministically" $
      \(Digits ds) -> let str = intercalate "," (map pure ds) in
        greedy (sepBy greedyComma several greedyDigit) str
          === Just (ds, "")
        .&&. greedy (sepBy greedyComma (atLeast 1) greedyDigit) str
          === (if null ds then Nothing else Just (ds, ""))
    prop "manyTillP p q parses some p, then q" $
      \(Digits ds) ->
        parses (rmap Identity (manyTillP plainDigit (Joker ("!" <$ char '!')))) (ds ++ "!")
          === [ds ++ "!"]
    prop "manyTillP tries the rest first, deterministically" $
      \(Digits ds) ->
        greedy (manyTillP greedyDigit (Joker (pure []))) ds === Just ("", ds)
    it "sepBy sep ditraversed separates a fixed product's foci" $ do
      let pair = sepBy comma ditraversed plainDigit
            :: Joker ReadP (Product Identity Identity Char) (Product Identity Identity Char)
          full str = [x | (x, "") <- readP_to_S (runJoker pair) str]
      full "1,2" `shouldBe` [Pair (Identity '1') (Identity '2')]
      full "12" `shouldBe` []
    prop "atLeast n parses exactly the digit strings of at least n" $
      \(Digits ds) (Small k) -> let n = abs k `mod` 6 in
        parses (rmap Identity (atLeast n >?* plainDigit)) ds
          === [ds | length ds >= n]
    prop "atMost n parses exactly the digit strings of at most n" $
      \(Digits ds) (Small k) -> let n = abs k `mod` 6 in
        parses (rmap Identity (atMost n >?* plainDigit)) ds
          === [ds | length ds <= n]
    prop "exactly n >?* p = replicateP n p" $
      \(Digits ds) (Small k) -> let n = abs k `mod` 6 in
        parses (rmap Identity (exactly n >?* plainDigit)) ds
          === parses (rmap Identity (replicateP n plainDigit :: Joker ReadP String String)) ds
    prop "inRange lo hi parses exactly the digit strings of lo to hi" $
      \(Digits ds) (Small a) (Small b) -> let lo = abs a `mod` 6; hi = abs b `mod` 6 in
        parses (rmap Identity (inRange lo hi >?* plainDigit)) ds
          === [ds | lo <= length ds, length ds <= hi]
    prop "sepBy sep (atLeast n) & (atMost n) bound separated digits" $
      \(Digits ds) (Small k) -> let n = abs k `mod` 6; str = bracketed ds in
        parses (rmap Identity (inBrackets (sepBy comma (atLeast n) plainDigit))) str
          === [ds | length ds >= n]
        .&&. parses (rmap Identity (inBrackets (sepBy comma (atMost n) plainDigit))) str
          === [ds | length ds <= n]
    prop "skippedOptional skips a trailing separator, or none" $
      \(Digits ds) -> let
          trailing = rmap Identity ((several >?* plainDigit) *< (skippedOptional >?* comma))
        in parses trailing ds === [ds] .&&. parses trailing (ds ++ ",") === [ds]
    prop "sepBy is ambiguous only where its Prismoid is" $
      \(Digits ds0) -> let ds = take 8 ds0 in
        length (parses (rmap Identity (sepBy comma (atLeast 1 . atLeast 1) plainDigit)) (intercalate "," (map pure ds)))
          === length (parses ((atLeast 1 . atLeast 1) digit) ds)

newtype Digits = Digits String deriving Show
instance Arbitrary Digits where
  arbitrary = Digits <$> listOf (elements ['0' .. '9'])

bracketed :: String -> String
bracketed ds = "[" ++ intercalate "," (map pure ds) ++ "]"

inBrackets :: Joker ReadP a b -> Joker ReadP a b
inBrackets p = Joker (() <$ char '[') >* p *< Joker (() <$ char ']')

comma :: Joker ReadP () ()
comma = Joker (() <$ char ',')

digit :: Joker ReadP Char (Identity Char)
digit = rmap Identity plainDigit

plainDigit :: Joker ReadP Char Char
plainDigit = Joker (satisfy isDigit)

data Tree = Leaf Char | Node Tree Tree deriving (Eq, Show)

_Node :: Prism' Tree (Tree, Tree)
_Node = prism' (uncurry Node) (\case Node x y -> Just (x, y); _ -> Nothing)

plainLeaf :: Joker ReadP Tree Tree
plainLeaf = Joker (Leaf <$> satisfy isDigit)

-- | A deterministic parser, committing to its first success.
type Greedy = Joker (StateT String Maybe)

greedyDigit :: Greedy Char Char
greedyDigit = Joker (StateT (\case c : cs | isDigit c -> Just (c, cs); _ -> Nothing))

greedyComma :: Greedy () ()
greedyComma = Joker (StateT (\case ',' : cs -> Just ((), cs); _ -> Nothing))

greedy :: Greedy s t -> String -> Maybe (t, String)
greedy = runStateT . runJoker

parses :: Joker ReadP s (Identity t) -> String -> [t]
parses p str = [x | (Identity x, "") <- readP_to_S (runJoker p) str]
