module Properties.Filtrator
  ( filtratorSpec
  ) where

import Control.Lens.Grammar
import Data.Profunctor (unleft, unright)
import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck

{- | `filtrate` is a retraction of `alternate`,

prop> unleft . left' = id
prop> unright . right' = id

for every interpreter, observed by its whole state, & a retraction
of `>+<` for those which try both summands, like `Printor` & `Parsor` @s []@.
-}
filtratorSpec :: Spec
filtratorSpec = describe "Filtrator" $ do
  describe "unleft . left' = id" $ do
    prop "prints, by Printor" $ \c ->
      printed (unleft (left' ab)) c === printed ab c
    prop "prints, by Parsector" $ \c ->
      unparsec (unleft (left' ab)) c === unparsec ab c
    prop "parses, by Parsector" $ forAll input $ \str ->
      parsec (unleft (left' ab)) str === parsec ab str
    prop "parses, by Parsor" $ forAll input $ \str ->
      parsedMaybe (unleft (left' ab)) str === parsedMaybe ab str
      .&&. parsedList (unleft (left' ab)) str === parsedList ab str
  describe "unright . right' = id" $ do
    prop "prints, by Printor" $ \c ->
      printed (unright (right' ab)) c === printed ab c
    prop "prints, by Parsector" $ \c ->
      unparsec (unright (right' ab)) c === unparsec ab c
    prop "parses, by Parsector" $ forAll input $ \str ->
      parsec (unright (right' ab)) str === parsec ab str
    prop "parses, by Parsor" $ forAll input $ \str ->
      parsedMaybe (unright (right' ab)) str === parsedMaybe ab str
      .&&. parsedList (unright (right' ab)) str === parsedList ab str
  describe "filtrate (x >+< y) = (x, y)" $ do
    prop "prints, by Printor" $ \c ->
      printed (fst (filtrate (ab >+< bc))) c === printed ab c
      .&&. printed (snd (filtrate (ab >+< bc))) c === printed bc c
    prop "parses, by Parsor s []" $ forAll input $ \str ->
      parsedList (fst (filtrate (ab >+< bc))) str === parsedList ab str
      .&&. parsedList (snd (filtrate (ab >+< bc))) str === parsedList bc str
  where
    ab, bc :: Grammar Char Char
    ab = oneOf "ab"
    bc = oneOf "bc"
    input = do
      n <- choose (0, 3)
      vectorOf n (elements "abcd")

printed :: Printor String Maybe a b -> a -> Maybe String
printed p a = ($ "") <$> printP p a

-- | The whole state of a Parsector.
type State b = (Bool, Word, String, ParsecFailure String, Maybe b)

state :: ParsecState String b -> State b
state (ParsecState looked offset stream failure result) =
  (looked, offset, stream, failure, result)

unparsec :: Parsector String a b -> a -> State b
unparsec p a = state (unparsecP p a "")

parsec :: Parsector String a b -> String -> State b
parsec p str = state (parsecP p str)

parsedMaybe :: Parsor String Maybe a b -> String -> Maybe (b, String)
parsedMaybe = parseP

parsedList :: Parsor String [] a b -> String -> [(b, String)]
parsedList = parseP
