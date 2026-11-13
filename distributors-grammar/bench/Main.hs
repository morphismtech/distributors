{- | Benchmarks of @distributors@' core combinators, at the grammar
backends which run them: parsing by @Parsor@ & @Parsector@, printing
by @Printor@ & @Parsector@, & building static @Grammor@s.

Every benchmark checks its result against an expected value, which
forces it fully; a backend which doesn't round-trip a workload in
setup is skipped, & reported.
-}
module Main (main) where

import Control.Lens
import Control.Lens.Grammar
import Control.Lens.Comonocle (_BoundedEnum, indexComonocle)
import Control.Monad (unless)
import Data.List (intercalate)
import Test.Tasty.Bench

import Examples.Arithmetic
import Examples.Expression
import Examples.Heredoc
import Examples.Json
import Examples.Lambda
import Examples.SemVer
import Examples.SExpr

main :: IO ()
main = do
  groups <- sequence
    [ backends "repeat" repeats
    , backends "separate" separates
    , backends "varifocal" varifocals
    , backends "example" examples
    , pure statics
    , pure optics
    ]
  defaultMain groups

-- | A named workload: a grammar, an input string & its syntax value.
data Workload = forall a. Eq a => Workload String (CtxGrammar Char a) String a

-- | Benchmark each workload at each backend which round-trips it.
backends :: String -> [Workload] -> IO Benchmark
backends name workloads = bgroup name . concat <$> traverse workload workloads
  where
    workload (Workload wname g str a) =
      fmap catMaybes . traverse keep $ cases wname g str a
    keep (backend, ok, b) = do
      unless ok $ putStrLn ("skipped: " <> name <> "/" <> backend)
      pure (if ok then Just b else Nothing)

cases
  :: forall a. Eq a
  => String -> CtxGrammar Char a -> String -> a
  -> [(String, Bool, Benchmark)]
cases wname g str a =
  [ ( wname <> "/parse"
    , fmap fst (parser str) == Just a
    , bench (wname <> "/parse") $
        whnf (\s -> fmap fst (parser s) == Just a) str )
  , ( wname <> "/print"
    , fmap ($ "") (printer a) == Just str
    , bench (wname <> "/print") $
        whnf (\x -> fmap (\pr -> length (pr "")) (printer x)) a )
  , ( wname <> "/parsec"
    , parsecResult (parsector str) == Just a
    , bench (wname <> "/parsec") $
        whnf (\s -> parsecResult (parsector s) == Just a) str )
  , ( wname <> "/unparsec"
    , parsecStream (unparsector a "") == str
    , bench (wname <> "/unparsec") $
        whnf (\x -> length (parsecStream (unparsector x ""))) a )
  ]
  where
    parser :: String -> Maybe (a, String)
    parser = parseG g
    printer :: a -> Maybe (String -> String)
    printer = printG g
    parsector :: String -> ParsecState String a
    parsector = parsecG g
    unparsector :: a -> String -> ParsecState String a
    unparsector = unparsecG g

digitG :: RegGrammar Char Char
digitG = asIn @Char DecimalNumber

commaG :: RegGrammar Char ()
commaG = terminal ","

size :: Int
size = 1000

digits :: String
digits = take size (cycle ['0' .. '9'])

commaDigits :: String
commaDigits = intercalate "," (map pure digits)

-- | Repetition, by the classes' methods & by Prismoids.
repeats :: [Workload]
repeats =
  [ Workload "manyP" (manyP digitG) digits digits
  , Workload "someP" (someP digitG) digits digits
  , Workload "several" (several >?* digitG) digits digits
  , Workload "atLeast 1" (atLeast 1 >?* digitG) digits digits
  , Workload "atLeast 500" (atLeast 500 >?* digitG) digits digits
  , Workload "atMost" (atMost size >?* digitG) digits digits
  , Workload "exactly" (exactly size >?* digitG) digits digits
  , Workload "replicateP" (replicateP size digitG) digits digits
  , Workload "clonePrismoid atLeast 1" (clonePrismoid (atLeast 1) >?* digitG) digits digits
  , Workload "manyTillP" (manyTillP digitG (terminal "." >* asEmpty)) (digits <> ".") digits
  , Workload "skipManyP" (skipManyP (terminal " ")) (replicate size ' ') ()
  ]

-- | Separated repetition, by sepBy, & hand-rolled.
separates :: [Workload]
separates =
  [ Workload "sepBy several" (sepBy commaG several digitG) commaDigits digits
  , Workload "sepBy atLeast 1" (sepBy commaG (atLeast 1) digitG) commaDigits digits
  , Workload "sepBy exactly" (sepBy commaG (exactly size) digitG) commaDigits digits
  , Workload "hand-rolled" (digitG >:< manyP (commaG >* digitG) >|< asEmpty) commaDigits digits
  ]

-- | Varifocals, applied by contextually.
varifocals :: [Workload]
varifocals =
  [ Workload "terminateBy" (contextually (terminateBy (== '.')) (anyToken @Char))
      (digits <> ".") (digits <> ".")
  , Workload "balanceBy" (contextually (balanceBy (== '(') (== ')')) (anyToken @Char))
      nested nested
  , Workload "heredoc" heredocG heredocStr heredoc
  ]
  where
    nested = replicate 200 '(' <> replicate 200 ')'
    heredoc = Heredoc "EOF" (replicate 200 "some line of the body")
    heredocStr = "<<EOF\n" <> concatMap (<> "\n") (replicate 200 "some line of the body") <> "EOF\n"

-- | The test examples, scaled up.
examples :: [Workload]
examples =
  [ Workload "arith" arithGrammar arithStr (parsed arithGrammar arithStr)
  , Workload "expr" exprGrammar exprStr (parsed exprGrammar exprStr)
  , Workload "expr left-assoc" leftGrammar leftStr (parsed leftGrammar leftStr)
  , Workload "json" jsonGrammar jsonStr (parsed jsonGrammar jsonStr)
  , Workload "sexpr" sexprGrammar sexprStr (parsed sexprGrammar sexprStr)
  , Workload "lambda" lambdaGrammar lambdaStr (parsed lambdaGrammar lambdaStr)
  , Workload "semver" semverCtxGrammar semverStr (parsed semverCtxGrammar semverStr)
  ]
  where
    parsed :: CtxGrammar Char a -> String -> a
    parsed g s = case parseG g s of
      Just (a, "") -> a
      _ -> error ("bench input doesn't parse: " <> take 40 s)
    terms n ops = concat
      [ show (i `mod` 97) <> [ops !! (i `mod` length ops)] | i <- [1 .. n] ] <> "1"
    arithStr = terms 300 "+*"
    exprStr = terms 300 "+-*/^"
    leftStr = terms 300 "+-*/"
    jsonStr = "[" <> intercalate ","
      (replicate 100 "{\"a\":[1,2,3],\"b\":\"text\",\"c\":true,\"d\":null}") <> "]"
    sexprStr = "(" <> unwords (replicate 200 "(foo (bar baz) qux)") <> ")"
    lambdaStr = foldr (\v body -> "\\" <> v <> "." <> body) "x"
      [ "x" <> show i | i <- [1 .. 100 :: Int] ]
    semverStr = "1.22.333-alpha.beta.1.2.3+build.7.sha.abcdef"

-- | Building static grammars, as regular expressions & Backus-Naur forms.
statics :: Benchmark
statics = bgroup "static"
  [ bench "regstring sepBy" $ whnf (length . show . regstringG) (sepBy commaG several digitG)
  , bench "regbnf json" $ whnf (length . show . regbnfG) jsonGrammar
  , bench "regbnf expr" $ whnf (length . show . regbnfG) exprGrammar
  ]

-- | Optics as lenses, at functions.
optics :: Benchmark
optics = bgroup "optic"
  [ bench "over several" $ nf (over several succ) ints
  , bench "map" $ nf (map succ) ints
  , bench "over homogenized" $ nf (over homogenized succ) ints
  , bench "over crossDiopter" $ nf (over (crossDiopter several several) succ) (ints, ints)
  , bench "zipDiopter" $ nf (zipDiopter several (Just . sum)) [ints, ints, ints]
  , bench "indexComonocle" $ nf (map (view (indexComonocle _BoundedEnum))) ords
  , bench "withPrismoid" $ nf (\xs -> withPrismoid (atLeast 1) (\f g -> fmap g (f xs))) ints
  ]
  where
    ints = [1 .. size]
    ords = take size (cycle [LT, EQ, GT])
