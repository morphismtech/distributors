-- | A sum of records has partial fields.
{-# OPTIONS_GHC -Wno-partial-fields #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE RequiredTypeArguments #-}
module Properties.Char
  ( textualSpec
  ) where

import Control.Lens.Grammar
  ( LL1Conflict, ParsecState (..), RegBnf (..), RegString (..), conflictRule
  , liftBnf1, ll1Conflicts
  )
import Control.Lens.Grammar.Char.Redesign
import Control.Applicative (ZipList)
import Data.ByteString qualified as ByteString
import Data.ByteString.Lazy qualified as LByteString
import Data.Complex (Complex)
import Data.Fixed (Centi, Milli, Uni)
import Data.Functor.Compose (Compose)
import Data.Functor.Const (Const)
import Data.Functor.Identity (Identity)
import Data.Functor.Product qualified as Functor
import Data.Functor.Sum qualified as Functor
import Data.HashMap.Strict (HashMap)
import Data.HashSet (HashSet)
import Data.Int (Int8, Int64)
import Data.IntMap (IntMap)
import Data.IntSet (IntSet)
import Data.List.NonEmpty (NonEmpty)
import Data.Map (Map)
import Data.Monoid qualified as Monoid
import Data.Ord (Down)
import Data.Proxy (Proxy)
import Data.Semigroup qualified as Semigroup
import Data.Sequence (Seq)
import Data.Set (Set)
import Data.Text qualified as Text
import Data.Text.Lazy qualified as LText
import Data.Tree (Tree)
import Data.Vector (Vector)
import Data.Version (Version)
import Foreign.C.Types (CChar, CDouble, CFloat, CInt, CSize)
import System.Exit (ExitCode)
import System.IO (BufferMode, IOMode, SeekMode)
import Data.Ratio ((%))
import Data.Word (Word8)
import GHC.Generics (Generic)
import Numeric.Natural (Natural)
import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck
import Test.QuickCheck.Instances ()
import Text.Read (readMaybe)

-- | A sum of prefix & record constructors.
data T
  = A
  | B Int (Maybe Bool)
  | R {f :: Int, g :: String}
  deriving stock (Eq, Show, Read, Generic)
  deriving anyclass Textual

instance Arbitrary T where
  arbitrary = oneof
    [pure A, B <$> arbitrary <*> arbitrary, R <$> arbitrary <*> arbitrary]

-- | Infix constructors, of one fixity, with operands of other types.
data I = Int :+: Int | Bool :* I | Char `Cat` I | Nil
  deriving stock (Eq, Show, Read, Generic)
  deriving anyclass Textual
infixr 5 :+:, :*, `Cat`

instance Arbitrary I where
  arbitrary = sized $ \n -> oneof $
    [pure Nil, (:+:) <$> arbitrary <*> arbitrary]
    <> [ (:*) <$> arbitrary <*> resize (n `div` 2) arbitrary | n > 0 ]
    <> [ Cat <$> arbitrary <*> resize (n `div` 2) arbitrary | n > 0 ]

-- | Constructors whose names prefix each other.
data N = Foo | Foobar | Fo Int
  deriving stock (Eq, Show, Read, Generic)
  deriving anyclass Textual

instance Arbitrary N where
  arbitrary = oneof [pure Foo, pure Foobar, Fo <$> arbitrary]

-- | A recursive type, recurring through lists.
data Rose = Rose Int [Rose]
  deriving stock (Eq, Show, Read, Generic)
  deriving anyclass Textual

instance Arbitrary Rose where
  arbitrary = sized $ \n -> Rose <$> arbitrary
    <*> resize (n `div` 3) (listOf (resize (n `div` 3) arbitrary))

-- | A record with an operator field & a negative default.
data Op = Op {(%%) :: Double, plain :: Maybe Integer}
  deriving stock (Eq, Show, Read, Generic)
  deriving anyclass Textual

instance Arbitrary Op where
  arbitrary = Op <$> arbitrary <*> arbitrary

{- | A type's `Textual` grammar agrees with its `Show` & `Read` instances:
it prints as `show` does, by its printers, parses what `show` prints,
parses whitespace & parentheses as `read` does, and is @LL(1)@.
-}
compat
  :: forall a. (Textual a, Show a, Read a, Arbitrary a)
  => String -> (a -> a -> Bool) -> Spec
compat name same = compatWith @a name same True

{- | Like `compat`, for types which start with a parenthesis, whose
redundant parentheses aren't parsed, unlike @read@.
-}
compatParenthesized
  :: forall a. (Textual a, Show a, Read a, Arbitrary a)
  => String -> (a -> a -> Bool) -> Spec
compatParenthesized name same = compatWith @a name same False

compatWith
  :: forall a. (Textual a, Show a, Read a, Arbitrary a)
  => String -> (a -> a -> Bool) -> Bool -> Spec
compatWith name same redundant = describe name $ do
  prop "prints as show does" $ \(a :: a) ->
    charShowsPrec 0 a "" === show a
  prop "prints as showsPrec 11 does" $ \(a :: a) ->
    charShowsPrec 11 a "" === showsPrec 11 a ""
  prop "prints predictively as show does" $ \(a :: a) ->
    parsecStream (charUnparsecPrec @a @String 0 a) === show a
  prop "prints by backtracking as show does" $ \(a :: a) ->
    charUnparsePrec @a @Maybe 0 a "" === Just (show a)
  prop "parses predictively what show prints" $ \(a :: a) ->
    maybe False (same a) (parsed 0 (show a))
  prop "parses whitespace as read does" $ \(a :: a) ->
    forAll (spaced (show a)) $ \str -> agrees str
  if redundant
    then prop "parses parentheses as read does" $ \(a :: a) ->
      forAll (spaced ("(" <> show a <> ")")) $ \str -> agrees str
    else prop "parses parentheses once required" $ \(a :: a) ->
      maybe False (same a) (parsed 11 (showsPrec 11 a ""))
  it "is LL(1)" $
    map conflictRule (conflicts (charGrammarPrec 0 (type a))) `shouldBe` []
  where
    {- predictively, by Parsector, & by backtracking, by Parsor,
    which may consume trailing whitespace in several ways -}
    agrees str = counterexample str $
      case (readMaybe @a str, parsed 0 str, readsAll str) of
        (Nothing, Nothing, []) -> property True
        (Just x, Just y, zs@(_ : _)) -> property (same x y && all (same x) zs)
        (x, y, z) -> counterexample (show (x, y, z)) False
    readsAll str =
      [a | (a, rest) <- charReadsPrec 0 str, all (`elem` blank) rest]
    blank = " \t\n" :: String

-- | A complete predictive parse, by `Parsector`, at a precedence.
parsed :: forall a. Textual a => Int -> String -> Maybe a
parsed d str = case charParsecPrec d str of
  ParsecState {parsecStream = "", parsecResult = Just a} -> Just a
  _ -> Nothing

-- | A string with whitespace inserted anywhere.
spaced :: String -> Gen String
spaced str = do
  n <- choose (0, 3 :: Int)
  go n str
  where
    go 0 s = pure s
    go n s = do
      i <- choose (0, length s)
      w <- elements [" ", "\t", "\n", "  "]
      let (l, r) = splitAt i s
      go (n - 1) (l <> w <> r)

conflicts :: RegBnf -> [LL1Conflict Char]
conflicts = ll1Conflicts . liftBnf1 runRegString . runRegBnf

textualSpec :: Spec
textualSpec = describe "Textual" $ do
  compatParenthesized @() "()" (==)
  compat @Bool "Bool" (==)
  compat @Ordering "Ordering" (==)
  compat @Char "Char" (==)
  compat @String "String" (==)
  compat @Int "Int" (==)
  compat @Int8 "Int8" (==)
  compat @Int64 "Int64" (==)
  compat @Word8 "Word8" (==)
  compat @Integer "Integer" (==)
  compat @Natural "Natural" (==)
  compat @Double "Double" sameFloat
  compat @Float "Float" sameFloat
  compatParenthesized @Rational "Rational" (==)
  compat @(Maybe Int) "Maybe Int" (==)
  compat @(Either Int String) "Either Int String" (==)
  compat @[Maybe Bool] "[Maybe Bool]" (==)
  compatParenthesized @(Int, Char) "(Int, Char)" (==)
  compatParenthesized @(Bool, (), Maybe Int) "(Bool, (), Maybe Int)" (==)
  compatParenthesized @(Int, Int, Int, Int, Int, Int, Int) "7-tuples" (==)
  compatParenthesized @(Int, Int, Int, Int, Int, Int, Int, Int, Int, Int)
    "10-tuples" (==)
  compat @(Identity Int) "Identity" (==)
  compat @(Const Int Bool) "Const" (==)
  compat @(Down Int) "Down" (==)
  compat @(Compose Maybe [] Int) "Compose" (==)
  compat @(Proxy Int) "Proxy" (==)
  compat @(NonEmpty Int) "NonEmpty" (==)
  compatParenthesized @(Complex Double) "Complex" sameFloat
  compat @(Tree Int) "Tree" (==)
  compat @(ZipList Int) "ZipList" (==)
  compat @Version "Version" (==)
  compat @ExitCode "ExitCode" (==)
  compat @IOMode "IOMode" (==)
  compat @SeekMode "SeekMode" (==)
  compat @BufferMode "BufferMode" (==)
  compat @(Monoid.Sum Int) "Sum" (==)
  compat @(Monoid.Product Int) "Product" (==)
  compat @(Monoid.First Int) "First" (==)
  compat @(Monoid.Alt Maybe Int) "Alt" (==)
  compat @Monoid.Any "Any" (==)
  compat @(Semigroup.Min Int) "Min" (==)
  compat @(Semigroup.Arg Int Char) "Arg" (==)
  compat @(Functor.Product Maybe [] Int) "functor Product" (==)
  compat @(Functor.Sum Maybe [] Int) "functor Sum" (==)
  compat @Milli "Milli" (==)
  compat @Centi "Centi" (==)
  compat @Uni "Uni" (==)
  compat @CInt "CInt" (==)
  compat @CChar "CChar" (==)
  compat @CSize "CSize" (==)
  compat @CDouble "CDouble" sameFloat
  compat @CFloat "CFloat" sameFloat
  compat @(Map Int Char) "Map" (==)
  compat @(Set Int) "Set" (==)
  compat @(IntMap Bool) "IntMap" (==)
  compat @IntSet "IntSet" (==)
  compat @(Seq Int) "Seq" (==)
  compat @(HashMap Int Int) "HashMap" (==)
  compat @(HashSet Int) "HashSet" (==)
  compat @Text.Text "Text" (==)
  compat @LText.Text "lazy Text" (==)
  compat @ByteString.ByteString "ByteString" (==)
  compat @LByteString.ByteString "lazy ByteString" (==)
  compat @(Vector Int) "Vector" (==)
  compat @T "sums of prefix & record constructors" (==)
  compatParenthesized @I "infix constructors" (==)
  compat @N "constructors prefixing each other" (==)
  compat @Rose "recursive types" (==)
  compat @Op "records with operator fields" sameOp
  describe "examples" $ do
    it "parses read's literals" $ do
      parsed @Int 0 "0x1F" `shouldBe` Just 31
      parsed @Int 0 "0b101" `shouldBe` Just 5
      parsed @Double 0 "1.5E+2" `shouldBe` Just 150
      parsed @Rational 0 "-3 % -4" `shouldBe` Just (3 % 4)
      parsed @String 0 "\"\\SO\\&H\\1234\\&5\""
        `shouldBe` Just "\SO\&H\1234\&5"
      parsed @String 0 "\"a\\   \\b\"" `shouldBe` Just "ab"
    it "separates words as read does" $ do
      parsed @(Maybe Int) 0 "Just1" `shouldBe` Nothing
      parsed @(Maybe Int) 0 "Just(1)" `shouldBe` Just (Just 1)
      parsed @(Maybe Int) 0 "Just -1" `shouldBe` Just (Just (-1))
      parsed @T 0 "B 1Nothing" `shouldBe` Just (B 1 Nothing)
      parsed @N 0 "Foob" `shouldBe` Nothing
  where
    sameFloat x y = show x == show y
    sameOp (Op x i) (Op y j) = sameFloat x y && i == j
