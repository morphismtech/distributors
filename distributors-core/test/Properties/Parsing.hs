module Properties.Parsing (parsingProperties) where

import Control.Lens.Diopter (manied)
import Control.Lens.Prismoid
import Data.Bifunctor.Joker (Joker (..))
import Data.Char (isDigit)
import Data.Functor.Identity (Identity (..))
import Data.List (intercalate)
import Control.Lens (Prism', prism')
import Data.Profunctor (rmap)
import Data.Profunctor.Distributor (SepBy (..), chain1, intercalateP, sepBy, several, several1)
import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck
import Text.ParserCombinators.ReadP (ReadP, char, readP_to_S, satisfy)

parsingProperties :: Spec
parsingProperties = do
  describe "separated" $ do
    prop "separated somed = several1" $ \(Digits ds) ->
      let str = bracketed ds
      in parses (rmap Identity (separated somed brackets plainDigit)) str
          === parses (rmap Identity (several1 brackets plainDigit :: Joker ReadP String String)) str
    prop "separated manied = several" $ \(Digits ds) ->
      let str = bracketed ds
      in parses (rmap Identity (separated manied brackets plainDigit)) str
          === parses (rmap Identity (several brackets plainDigit :: Joker ReadP String String)) str
    prop "separated (intercalated n) = intercalateP n" $
      \(Digits ds) -> let str = bracketed ds; n = length ds in
        parses (rmap Identity (separated (intercalated n) brackets plainDigit :: Joker ReadP String String)) str
          === parses (rmap Identity (intercalateP n brackets plainDigit)) str
    prop "separated (chained1 assoc pat) = chain1 assoc pat" $
      \(Digits ds) -> let str = bracketed ds in
        parses (rmap Identity (separated (chained1 Left _Node) brackets plainLeaf)) str
          === parses (rmap Identity (chain1 Left _Node brackets plainLeaf)) str
        .&&. parses (rmap Identity (separated (chained1 Right _Node) brackets plainLeaf)) str
          === parses (rmap Identity (chain1 Right _Node brackets plainLeaf)) str
    prop "separated somed parses only separated digits" $
      \(Digits ds) -> parses (rmap Identity (separated somed brackets plainDigit)) (bracketed ds)
        === [ds | not (null ds)]
    prop "separated is ambiguous only where its Prismoid is" $
      \(Digits ds0) -> let ds = take 8 ds0 in
        length (parses (rmap Identity (separated (somed . somed) (sepBy comma) plainDigit)) (intercalate "," (map pure ds)))
          === length (parses ((somed . somed) digit) ds)

newtype Digits = Digits String deriving Show
instance Arbitrary Digits where
  arbitrary = Digits <$> listOf (elements ['0' .. '9'])

bracketed :: String -> String
bracketed ds = "[" ++ intercalate "," (map pure ds) ++ "]"

brackets :: SepBy (Joker ReadP () ())
brackets = SepBy (sym '[') (sym ']') (sym ',')
  where sym c = Joker (() <$ char c)

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

parses :: Joker ReadP s (Identity t) -> String -> [t]
parses p str = [x | (Identity x, "") <- readP_to_S (runJoker p) str]
