module Main (main) where

import Data.Foldable hiding (toList)
import Control.Lens.Grammar
import Data.Bifunctor.Joker (Joker (..))
import Control.Monad (when)
import Data.List (genericLength)
import Data.Tree (Tree (..))
import Data.String (fromString)
import GHC.Exts (toList)
import Text.ParserCombinators.ReadP (readP_to_S)
import Text.ParserCombinators.ReadPrec (ReadPrec, readPrec_to_S)
import Data.Functor.Contravariant (Predicate (..))
import Test.Hspec
import Test.Hspec.QuickCheck (modifyMaxSize, prop)
import Test.QuickCheck (Gen, choose, elements, forAll, generate, listOf, oneof, (===))
import qualified Text.Megaparsec as M

import Examples.Arithmetic
import Examples.Chain
import Examples.Expression
import Examples.Json
import Examples.Lambda
import Examples.LenVec
import Examples.RegString
import Examples.Rho
import Examples.SemVer
import Examples.SExpr
import Properties.Base
import Properties.Kleene
import Properties.Varifocal

main :: IO ()
main = hspec $ do
  describe "regexGrammar" $ testCfg False regexExamples (grammar @Char)
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
  describe "rhoGrammar" $ testCfg True rhoExamples rhoGrammar
  describe "rholangGrammar" $ testCfg True rholangExamples rholangGrammar
  describe "parseForest" parseForestTests
  describe "Parsector try rollback" tryRollbackTests
  describe "Kleene" kleeneProperties
  describe "Varifocal" varifocalProperties
  describe "class runners, at Arith's Grammar" classRunnerTests
  describe "ReadPrec & Predicate" readPrecTests
  describe "base types" baseProperties
  describe "RegEx ranges & try" regexRangeTryTests
  describe "RegEx quantifiers" regexQuantifierTests
  describe "tokenRange" tokenRangeTests

regexRangeTryTests :: Spec
regexRangeTryTests = do
  it "parses classes listed or ranged alike" $ do
    (fromString "[abc]" :: RegEx Char) `shouldBe` oneOf "abc"
    (fromString "[a-c]" :: RegEx Char) `shouldBe` oneOf "abc"
    (fromString "[c-ab]" :: RegEx Char) `shouldBe` oneOf "b"
  it "escapes a literal dash in a class" $ do
    toList (oneOf "+-" :: RegEx Char) `shouldBe` "[\\+\\-]"
    (fromString "[\\+\\-]" :: RegEx Char) `shouldBe` oneOf "+-"
  it "renders a huge class by its runs" $
    toList (tokenClass (oneOf ['\x20' .. '\x10FFFF'] >&< notOneOf "\"\\") :: RegEx Char)
      `shouldSatisfy` ((< 40) . length)
  it "records try, rendering it" $ do
    let rex = try (terminal "ab") >|< terminal "ac" :: RegEx Char
    toList rex `shouldBe` "\\t{ab}|ac"
    fromString (toList rex) `shouldBe` rex
    "ac" =~ rex `shouldBe` True
  it "resolves an LL(1) conflict by try" $ do
    map conflictSort (ll1Conflicts (fromString "{start} = ab|ac" :: Bnf (RegEx Char)))
      `shouldBe` [LL1FirstFirst]
    ll1Conflicts (fromString "{start} = \\t{ab}|ac" :: Bnf (RegEx Char)) `shouldBe` []

tokenRangeTests :: Spec
tokenRangeTests = do
  let near = choose ('\0', '\x3FF')
  prop "tokenRange lo hi = oneOf [lo .. hi], as TokenClass" $ forAll near $ \lo -> forAll near $ \hi ->
    (tokenRange lo hi :: TokenClass Char) === oneOf [lo .. hi]
  prop "tokenRange lo hi = oneOf [lo .. hi], as a predicate" $ forAll near $ \lo -> forAll near $ \hi -> forAll near $ \x ->
    tokenRange lo hi x === (oneOf [lo .. hi] :: Char -> Bool) x
  it "renders as a range, & parses so" $ do
    toList (tokenRange 'a' 'z' :: RegEx Char) `shouldBe` "[a-z]"
    (fromString "[a-z]" :: RegEx Char) `shouldBe` tokenRange 'a' 'z'
    toList (tokenRange 'z' 'a' :: RegEx Char) `shouldBe` "[]"
  it "takes all of Unicode by its ends" $ do
    let rex = tokenClass (tokenRange '\x20' '\x10FFFF' >&< notOneOf "\"\\") :: RegEx Char
    toList rex `shouldBe` "[ !#-Z\\[\\]\\^_-\1114111]"
    map (=~ rex) ["a", "\"", "\x10FFFF", "\x1F"] `shouldBe` [True, False, True, False]
  prop "generates tokens in range" $ forAll (choose ('a', 'm')) $ \lo ->
    forAll (tokenRange lo 'z' :: Gen Char) $ \x -> lo <= x && x <= 'z'

regexQuantifierTests :: Spec
regexQuantifierTests = do
  let rendered :: Prismoid String String Char Char -> String
      rendered pat = toList (runGrammor (pat >?* Grammor (token 'a')) :: RegEx Char)
  it "renders counted Prismoids by their counts" $ do
    rendered (exactly 4) `shouldBe` "a{4}"
    rendered (atLeast 2) `shouldBe` "a{2,}"
    rendered (inRange 2 (Just 5)) `shouldBe` "a{2,5}"
    rendered (atMost 3) `shouldBe` "a{0,3}"
  it "renders the counts Kleene operators have by them" $ do
    rendered (atLeast 0) `shouldBe` "a*"
    rendered (atLeast 1) `shouldBe` "a+"
    rendered (atMost 1) `shouldBe` "a?"
    rendered (exactly 1) `shouldBe` "a"
    rendered (exactly 0) `shouldBe` ""
    rendered (inRange 3 (Just 2)) `shouldBe` "[]"
  it "parses counts, normalizing them" $ do
    (fromString "a{2,3}" :: RegEx Char) `shouldBe` timesK 2 (Just 3) (token 'a')
    toList (fromString "a{0,}" :: RegEx Char) `shouldBe` "a*"
    toList (fromString "a{1}" :: RegEx Char) `shouldBe` "a"
    toList (fromString "(ab){3}" :: RegEx Char) `shouldBe` "(ab){3}"
  it "matches counts" $ do
    let rex = fromString "a{2,3}" :: RegEx Char
    map (=~ rex) ["a", "aa", "aaa", "aaaa"] `shouldBe` [False, True, True, False]
    map (=~ (fromString "a{2,}" :: RegEx Char)) ["a", "aa", "aaaaa"]
      `shouldBe` [False, True, True]
  it "agrees on counts, negative or out of order, as RegEx, Grammor & Parsor" $
    for_ [(lo, hi) | lo <- [-3 .. 3], hi <- Nothing : map Just [-3 .. 3]] $ \(lo, hi) ->
      for_ (map (`replicate` 'a') [0 .. 4]) $ \w -> do
        let rex = timesK lo hi (token 'a') :: RegEx Char
            parsed = not (null [() | (_, "") <- parseP (inRange lo hi >?* (token 'a' :: Parsor String [] Char Char)) w])
            expected = length w >= lo && maybe True (length w <=) hi
        (w =~ rex, parsed) `shouldBe` (expected, expected)
        rendered (inRange lo hi) `shouldBe` toList rex
  prop "timesK n (Just n) x matches as n times x" $ \(x :: RegEx Char) ->
    forAll (choose (0, 3)) $ \n -> forAll (listOf (elements "ab")) $ \w ->
      (w =~ timesK n (Just n) x) === (w =~ mconcat (replicate n x))
  modifyMaxSize (const 8) $ prop "x{lo,hi} round trips through its string" $ \(x :: RegEx Char) ->
    forAll (choose (0, 3)) $ \lo -> forAll (oneof [pure Nothing, Just <$> choose (lo, 4)]) $ \hi ->
      let rex = timesK lo hi x in fromString (toList rex) === rex

readPrecTests :: Spec
readPrecTests = do
  it "runs a grammar at ReadPrec as at ReadP" $ for_ arithExamples $ \(syntax, string) ->
    [x | (x, "") <- readPrec_to_S (runJoker (arithGrammar :: Joker ReadPrec Arith Arith)) 0 string]
      `shouldBe` [syntax]
  it "tests a token class as a Predicate, as a function" $ do
    let cls = oneOf "abc" >&< notOneOf "b" :: TokenClass Char
    map (getPredicate (tokenClass cls)) "abcd" `shouldBe` map (tokenClass cls) "abcd"

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
  tokenRange lo hi = WrapMega $ M.label ("in range " ++ show (lo, hi)) (M.satisfy (tokenRange lo hi))
instance Ruled (WrapMega a) where
  rule lbl (WrapMega p) = WrapMega (M.label lbl p)
instance BackusNaurForm (WrapMega a)
instance Tried (WrapMega a) where
  try (WrapMega p) = WrapMega (M.try p)
instance Filterable WrapMega where
  catMaybes m = m >>= maybe (fail "unrestricted filtration") pure
