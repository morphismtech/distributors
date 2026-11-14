module Main (main) where

import Data.Foldable hiding (toList)
import Control.Lens.Grammar
import Data.Bifunctor.Joker (Joker (..))
import Control.Monad (when)
import Data.List (genericLength)
import Data.Tree (Tree (..))
import Text.ParserCombinators.ReadP (readP_to_S)
import Test.Hspec
import Test.QuickCheck (generate)
import qualified Text.Megaparsec as M

import Examples.Arithmetic
import Examples.Chain
import Examples.Expression
import Examples.Json
import Examples.Lambda
import Examples.LenVec
import Examples.RegString
import Examples.SemVer
import Examples.SExpr
import Properties.Kleene
import Properties.Varifocal

main :: IO ()
main = hspec $ do
  describe "regexGrammar" $ testCfg False regexExamples regexGrammar
  describe "semverGrammar" $ testCfg True semverExamples semverGrammar
  describe "semverCtxGrammar" $ testCsg True semverExamples semverCtxGrammar
  describe "arithGrammar" $ testCfg True arithExamples arithGrammar
  describe "jsonGrammar" $ testCfg False jsonExamples jsonGrammar
  describe "sexprGrammar" $ testCfg True sexprExamples sexprGrammar
  describe "lambdaGrammar" $ testCfg True lambdaExamples lambdaGrammar
  describe "lenvecGrammar" $ testCsg True lenvecExamples lenvecGrammar
  describe "chainGrammar" $ testCfg True chainExamples chainGrammar
  describe "exprGrammar" $ testCfg True exprExamples exprGrammar
  describe "powGrammar" $ testCfg False powExamples powGrammar
  describe "leftGrammar" $ testCfg True leftExamples leftGrammar
  describe "parseForest" parseForestTests
  describe "Parsector try rollback" tryRollbackTests
  describe "Kleene" kleeneProperties
  describe "Varifocal" varifocalProperties
  describe "class runners, at Arith's Grammar" classRunnerTests

classRunnerTests :: Spec
classRunnerTests = for_ arithExamples $ \(syntax, string) ->
  it ("run as arithGrammar does, on " <> string) $ do
    [x | (x, "") <- parseG string] `shouldBe` [syntax]
    (($ "") <$> printG syntax) `shouldBe` Just string
    unparseG syntax "" `shouldBe` Just string
    parsecResult (parsecG string) `shouldBe` Just syntax
    parsecStream (unparsecG syntax "") `shouldBe` string
    regbnfG Arith `shouldBe` (runGrammor arithGrammar :: Bnf (RegEx Char))
    [x | (x, "") <- readP_to_S (readG @Arith) string] `shouldBe` [syntax]

parseForestTests :: Spec
parseForestTests = do
  it "returns the nested rule forest for a full parse" $ do
    let (actualForest, actualRest) = parseForest (transducerG Arith) "2*3+4;;;"
    actualForest `shouldBe`
      [ Node ("arith", 0, 5, "2*3+4")
          [ Node ("sum", 0, 5, "2*3+4")
              [ Node ("product", 0, 3, "2*3")
                  [ Node ("factor", 0, 1, "2")
                      [Node ("number", 0, 1, "2") []]
                  , Node ("factor", 2, 3, "3")
                      [Node ("number", 2, 3, "3") []]
                  ]
              , Node ("product", 4, 5, "4")
                  [ Node ("factor", 4, 5, "4")
                      [Node ("number", 4, 5, "4") []]
                  ]
              ]
          ]
      ]
    actualRest `shouldBe` ";;;"

tryRollbackTests :: Spec
tryRollbackTests = do
  it "rolls back parse stream/offset on failed try" $ do
    let actual = parsecP (try (tokens "ab")) "ax"
    parsecLooked actual `shouldBe` False
    parsecOffset actual `shouldBe` 0
    parsecStream actual `shouldBe` "ax"
    parsecResult actual `shouldBe` (Nothing :: Maybe String)
  it "rolls back unparse stream/offset on failed try" $ do
    let actual = unparsecP (try (tokens "ab")) "ax" ""
    parsecLooked actual `shouldBe` False
    parsecOffset actual `shouldBe` 0
    parsecStream actual `shouldBe` ""
    parsecResult actual `shouldBe` (Nothing :: Maybe String)

testCfg
  :: forall a. (Show a, Eq a)
  => Bool -> [(a, String)] -> (forall p. Grammatical Char p => p a a) -> Spec
testCfg isLL1 examples gram = do
  describe "examples" $ for_ examples $ \(expectedSyntax, expectedString) -> do
    testCtxGrammar isLL1 gram (expectedSyntax, expectedString)
    it ("should match " <> expectedString <> " correctly") $ do
      let actualMatch = expectedString =~ (runGrammor gram :: Bnf (RegEx Char))
      actualMatch `shouldBe` True
  it ("should " <> (if isLL1 then "" else "not ") <> "be LL(1), statically") $
    ll1Conflicts (runGrammor gram :: Bnf (RegEx Char))
      `shouldSatisfy` (if isLL1 then null else not . null)
  describe "transducerG" $ do
    it "should generate the hundred shorted valid words in a language" $ do
      let machine = transducer (runGrammor gram) :: Transducer Char
      generated <- generate (take 100 <$> languageSample machine)
      for_ generated $ \word -> do
        let fullParses = [() | (_, "") <- parseP (gram :: Parsor String [] a a) word]
        fullParses `shouldBe` [()]

testCsg
  :: (Show a, Eq a)
  => Bool -> [(a, String)] -> (forall p. CtxGrammatical Char p => p a a) -> Spec
testCsg isLL1 examples gram =
  describe "examples" $ for_ examples $ testCtxGrammar isLL1 gram

testCtxGrammar
  :: forall a. (Show a, Eq a)
  => Bool -> (forall p. CtxGrammatical Char p => p a a) -> (a, String) -> Spec
testCtxGrammar isLL1 gram (expectedSyntax, expectedString) = do
  it ("should parseG from " <> expectedString <> " correctly") $ do
    let actualSyntax =
          [parsed | (parsed, "") <- parseP (gram :: Parsor String [] a a) expectedString]
    actualSyntax `shouldBe` [expectedSyntax]
  it ("should unparseG to " <> expectedString <> " correctly") $ do
    let actualString =
          unparseP (gram :: Parsor String Maybe a a) expectedSyntax ""
    actualString `shouldBe` Just expectedString
  it ("should printG to " <> expectedString <> " correctly") $ do
    let actualString =
          ($ "") <$> printP (gram :: Printor String Maybe a a) expectedSyntax
    actualString `shouldBe` Just expectedString
  when isLL1 $ do
    it ("should parsecG from " <> expectedString <> " correctly") $ do
      let actualSyntax = parsecP (gram :: Parsector String a a) expectedString
      let expectedLength = genericLength expectedString
      let actualLooked = parsecLooked actualSyntax
      let actualFailure  = parsecFailure  actualSyntax
      actualSyntax `shouldBe`
        (ParsecState actualLooked expectedLength "" actualFailure (Just expectedSyntax))
    it ("should unparsecG to " <> expectedString <> " correctly") $ do
      let actualString = unparsecP (gram :: Parsector String a a) expectedSyntax ""
      let expectedLength = genericLength expectedString
      let actualLooked = parsecLooked actualString
      let actualFailure  = parsecFailure  actualString
      actualString `shouldBe`
        (ParsecState actualLooked expectedLength expectedString actualFailure (Just expectedSyntax))
    it ("should parse with megaparsec to " <> expectedString <> " correctly") $ do
      let megaparsec = unwrapMega (runJoker (gram :: Joker WrapMega a a))
      let actualSyntax = M.parse megaparsec "<megaparsec>" expectedString
      actualSyntax `shouldBe` Right expectedSyntax

newtype WrapMega a = WrapMega {unwrapMega :: M.Parsec String String a}
  deriving newtype
    ( Functor, Applicative, Alternative
    , Monad, MonadPlus, MonadFail
    )
instance TerminalSymbol Char (WrapMega ()) where
  terminal str = WrapMega (M.chunk str *> pure ())
instance TokenAlgebra Char (WrapMega Char) where
  tokenClass exam = WrapMega $ M.label (show exam) (M.satisfy (tokenClass exam))
instance Tokenized Char (WrapMega Char) where
  anyToken = WrapMega M.anySingle
  token = WrapMega . M.single
  oneOf = WrapMega . M.oneOf
  notOneOf = WrapMega . M.noneOf
  asIn cat = WrapMega $ M.label ("in category " ++ show cat)
    (M.satisfy (tokenClass (asIn cat)))
  notAsIn cat = WrapMega $ M.label ("not in category " ++ show cat)
    (M.satisfy (tokenClass (notAsIn cat)))
instance Ruled (WrapMega a) where
  rule lbl (WrapMega p) = WrapMega (M.label lbl p)
instance BackusNaurForm (WrapMega a)
instance Tried (WrapMega a) where
  try (WrapMega p) = WrapMega (M.try p)
instance Filterable WrapMega where
  catMaybes m = m >>= maybe (fail "unrestricted filtration") pure
