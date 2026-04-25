module Main (main) where

import Data.Foldable hiding (toList)
import Control.Lens.Grammar
import Control.Monad (when)
import Data.IORef
import Data.Function (fix)
import Data.List (genericLength)
import Data.Maybe (isJust)
import Data.Profunctor.Types (Star (..))
import Data.Tree (Tree (..))
import System.Environment (lookupEnv)
import Test.DocTest
import Test.Hspec
import Test.QuickCheck (generate)
import qualified Text.Megaparsec as M

import Examples.Arithmetic
import Examples.Chain
import Examples.Json
import Examples.Lambda
import Examples.LenVec
import Examples.RegString
import Examples.SemVer
import Examples.SExpr
import Properties.Kleene

main :: IO ()
main = do
  shouldRunDoctests <- isJust <$> lookupEnv "DISTRIBUTORS_RUN_DOCTESTS"
  hspec $ do
    when shouldRunDoctests $
      describe "doctest" $
        it "should run haddock examples" doctests
    describe "regexGrammar" $ testCfg False regexExamples regexGrammar
    describe "semverGrammar" $ testCfg True semverExamples semverGrammar
    describe "semverCtxGrammar" $ testCsg True semverExamples semverCtxGrammar
    describe "arithGrammar" $ testCfg True arithExamples arithGrammar
    describe "jsonGrammar" $ testCfg False jsonExamples jsonGrammar
    describe "sexprGrammar" $ testCfg True sexprExamples sexprGrammar
    describe "lambdaGrammar" $ testCfg True lambdaExamples lambdaGrammar
    describe "lenvecGrammar" $ testCsg True lenvecExamples lenvecGrammar
    describe "chainGrammar" $ testCfg True chainExamples chainGrammar
    describe "parseForestGen" parseForestGenTests
    describe "Parsector try rollback" tryRollbackTests
    describe "Kleene" kleeneProperties
    describe "meander" meanderProperties

parseForestGenTests :: Spec
parseForestGenTests = do
  it "returns the nested rule forest for a full parse" $ do
    let (actualForest, actualRest) = parseForestGen (transducerG arithGrammar) "2*3+4;;;"
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
    let actual = parsecG (try (tokens "ab")) "ax"
    parsecLooked actual `shouldBe` False
    parsecOffset actual `shouldBe` 0
    parsecStream actual `shouldBe` "ax"
    parsecResult actual `shouldBe` (Nothing :: Maybe String)
  it "rolls back unparse stream/offset on failed try" $ do
    let actual = unparsecG (try (tokens "ab")) "ax" ""
    parsecLooked actual `shouldBe` False
    parsecOffset actual `shouldBe` 0
    parsecStream actual `shouldBe` ""
    parsecResult actual `shouldBe` (Nothing :: Maybe String)

doctests :: IO ()
doctests = do
  stackExe <- lookupEnv "STACK_EXE"
  ghcEnvironment <- lookupEnv "GHC_ENVIRONMENT"
  let
    modulePaths =
      [ "src/Control/Lens/Grammar.hs" ]
    sourceDirs =
      [ "-isrc"
      , "-itest"
      ]
    packageEnvFlags = case ghcEnvironment of
      Just "-" -> []
      Just path -> ["-package-env=" <> path]
      Nothing -> []
    runnerFlags
      | isJust stackExe = []
      | otherwise = sourceDirs <> packageEnvFlags
    languageExtensions =
      [ "-XAllowAmbiguousTypes"
      , "-XArrows"
      , "-XConstraintKinds"
      , "-XDataKinds"
      , "-XDefaultSignatures"
      , "-XDeriveFoldable"
      , "-XDeriveFunctor"
      , "-XDeriveTraversable"
      , "-XDeriveGeneric"
      , "-XDerivingStrategies"
      , "-XDerivingVia"
      , "-XEmptyCase"
      , "-XFlexibleContexts"
      , "-XFlexibleInstances"
      , "-XFunctionalDependencies"
      , "-XGADTs"
      , "-XGeneralizedNewtypeDeriving"
      , "-XImportQualifiedPost"
      , "-XImpredicativeTypes"
      , "-XInstanceSigs"
      , "-XLambdaCase"
      , "-XMagicHash"
      , "-XMonoLocalBinds"
      , "-XQuantifiedConstraints"
      , "-XRankNTypes"
      , "-XRecursiveDo"
      , "-XScopedTypeVariables"
      , "-XStandaloneDeriving"
      , "-XStandaloneKindSignatures"
      , "-XTemplateHaskell"
      , "-XTupleSections"
      , "-XTypeApplications"
      , "-XTypeFamilies"
      , "-XTypeOperators"
      , "-XUndecidableInstances"
      , "-XUndecidableSuperClasses"
      ]
  for_ modulePaths $ \modulePath -> do
    putStr "Testing module documentation in "
    putStrLn modulePath
    doctest (modulePath : runnerFlags <> languageExtensions)

meanderProperties :: Spec
meanderProperties =
  it "preserves left-to-right traversal effects" $ do
    let input = ["h", "e", "l", "l", "o"]
    seenRef <- newIORef []
    let visit item = modifyIORef' seenRef (item :) >> pure ()
    units <- runStar (meander traverse (Star visit)) input
    seen <- reverse <$> readIORef seenRef
    seen `shouldBe` input
    units `shouldBe` replicate (length input) ()

testCfg :: (Show a, Eq a) => Bool -> [(a, String)] -> Grammar Char a -> Spec
testCfg isLL1 examples grammar = do
  describe "examples" $ for_ examples $ \(expectedSyntax, expectedString) -> do
    testCtxGrammar isLL1 grammar (expectedSyntax, expectedString)
    it ("should match " <> expectedString <> " correctly") $ do
      let actualMatch = expectedString =~ regbnfG grammar
      actualMatch `shouldBe` True
  describe "generated languageG" $ do
    it "should parses with exactly one full parse" $ do
      generated <- generate (take 100 <$> languageG grammar)
      for_ generated $ \word -> do
        let fullParses = [() | (_, "") <- parseG grammar word]
        fullParses `shouldBe` [()]

testCsg :: (Show a, Eq a) => Bool -> [(a, String)] -> CtxGrammar Char a -> Spec
testCsg isLL1 examples grammar =
  describe "examples" $ for_ examples $ testCtxGrammar isLL1 grammar

testCtxGrammar :: (Show a, Eq a) => Bool -> CtxGrammar Char a -> (a, String) -> Spec
testCtxGrammar isLL1 grammar (expectedSyntax, expectedString) = do
  it ("should parseG from " <> expectedString <> " correctly") $ do
    let actualSyntax = [parsed | (parsed, "") <- parseG grammar expectedString]
    actualSyntax `shouldBe` [expectedSyntax]
  it ("should unparseG to " <> expectedString <> " correctly") $ do
    let actualString = unparseG grammar expectedSyntax ""
    actualString `shouldBe` Just expectedString
  it ("should printG to " <> expectedString <> " correctly") $ do
    let actualString = ($ "") <$> printG grammar expectedSyntax
    actualString `shouldBe` Just expectedString
  when isLL1 $ do
    it ("should parsecG from " <> expectedString <> " correctly") $ do
      let actualSyntax = parsecG grammar expectedString
      let expectedLength = genericLength expectedString
      let actualLooked = parsecLooked actualSyntax
      let actualFailure  = parsecFailure  actualSyntax
      actualSyntax `shouldBe`
        (ParsecState actualLooked expectedLength "" actualFailure (Just expectedSyntax))
    it ("should unparsecG to " <> expectedString <> " correctly") $ do
      let actualString = unparsecG grammar expectedSyntax ""
      let expectedLength = genericLength expectedString
      let actualLooked = parsecLooked actualString
      let actualFailure  = parsecFailure  actualString
      actualString `shouldBe`
        (ParsecState actualLooked expectedLength expectedString actualFailure (Just expectedSyntax))
    it ("should parse with megaparsec to " <> expectedString <> " correctly") $ do
      let megaparsec = unwrapMega (monadG grammar)
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
instance BackusNaurForm (WrapMega a) where
  rule lbl (WrapMega p) = WrapMega (M.label lbl p)
  ruleRec lbl = rule lbl . fix
instance Filterable WrapMega where
  catMaybes m = m >>= maybe (fail "unrestricted filtration") pure
instance MonadTry WrapMega where
  try (WrapMega p) = WrapMega (M.try p)
