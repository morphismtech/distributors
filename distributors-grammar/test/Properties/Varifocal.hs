module Properties.Varifocal (varifocalProperties) where

import Control.Lens.Grammar
import Data.Char (digitToInt, isDigit)
import Data.Foldable (for_)
import Examples.Heredoc
import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck

varifocalProperties :: Spec
varifocalProperties = do
  let
    printed :: Varifocal' String Char -> String -> Maybe String
    printed v s =
      ($ "") <$> printP (contextuallyT v (anyToken :: Printor String Maybe Char Char)) s
    parsed :: Varifocal' String Char -> String -> Maybe (String, String)
    parsed v = parseP (contextuallyT v (anyToken :: Parsor String Maybe Char Char))
    ended :: Varifocal' String Char
    ended = terminatedBy (== '.')
    plain = Prelude.filter (/= '.') <$> arbitrary
  describe "MonadicTrans laws, at Printor & Parsor" $ do
    let
      printing :: Printor String Maybe Char b -> Char -> Maybe (b, String)
      printing q c = fmap ($ "") <$> runPrintor q c
      parsing :: Parsor String Maybe Char b -> String -> Maybe (b, String)
      parsing = parseP
      prToken = anyToken :: Printor String Maybe Char Char
      paToken = anyToken :: Parsor String Maybe Char Char
    prop "liftP . pure = pure" $ \(n :: Int) (c :: Char) (str :: String) ->
      printing (liftP (pure n)) c === printing (pure n) c
        .&&. parsing (liftP (pure n)) str === parsing (pure n) str
    prop "liftP (m >>= k) = liftP m >>= liftP . k" $
      \(m :: Maybe Int) (Fun _ k :: Fun Int (Maybe Int)) (c :: Char) (str :: String) ->
        printing (liftP (m >>= k)) c === printing (liftP m >>= liftP . k) c
          .&&. parsing (liftP (m >>= k)) str === parsing (liftP m >>= liftP . k) str
    prop "joinP (fmap pure p) = p" $ \(c :: Char) (str :: String) ->
      printing (joinP (fmap pure prToken)) c === printing prToken c
        .&&. parsing (joinP (fmap pure paToken)) str === parsing paToken str
  describe "terminatedBy" $ do
    prop "prints & parses up to its first end" $
      forAll plain $ \s -> forAll plain $ \rest ->
        printed ended (s ++ ".") === Just (s ++ ".")
          .&&. parsed ended (s ++ "." ++ rest) === Just (s ++ ".", rest)
    prop "doesn't print without an end" $
      forAll plain $ \s -> printed ended s === Nothing
    prop "doesn't print an early end" $
      forAll plain $ \s -> forAll plain $ \t ->
        printed ended (s ++ "." ++ t ++ ".") === Nothing
  describe "balanced & countPrefixed, by stepping" $ do
    let
      nested :: Varifocal' String Char
      nested = balanced (== '(') (== ')')
      counted :: Varifocal' String Char
      counted = countPrefixed (\c -> if isDigit c then digitToInt c else 0)
    it "balanced parses a nested block, leaving the rest" $
      parsed nested "(a(b)c)rest" `shouldBe` Just ("(a(b)c)", "rest")
    it "balanced prints only a balanced block" $ do
      printed nested "(a(b)c)" `shouldBe` Just "(a(b)c)"
      map (printed nested) ["(a(b)", "(a)b", "a", ")", ""] `shouldBe` replicate 5 Nothing
    prop "balanced round-trips nesting of any depth" $
      forAll (choose (1, 6)) $ \n -> let str = replicate n '(' ++ replicate n ')' in
        printed nested str === Just str .&&. parsed nested (str ++ ")") === Just (str, ")")
    it "countPrefixed reads as many as its first focus counts" $ do
      parsed counted "3abcd" `shouldBe` Just ("3abc", "d")
      parsed counted "0x" `shouldBe` Just ("0", "x")
      printed counted "2ab" `shouldBe` Just "2ab"
      map (printed counted) ["3ab", "1ab"] `shouldBe` [Nothing, Nothing]
    it "clones balanced, as it does" $ do
      let cloned :: Varifocal' String Char
          cloned = cloneVarifocal nested
          strs = ["(a(b)c)", "(a(b)", "a", "((x))"]
      map (printed cloned) strs `shouldBe` map (printed nested) strs
      map (parsed cloned) strs `shouldBe` map (parsed nested) strs
  describe "cloneVarifocal, by its free Varifocus" $ do
    prop "clones terminatedBy, printing & parsing as it does" $
      forAll plain $ \s -> forAll plain $ \t ->
        let cloned :: Varifocal' String Char
            cloned = cloneVarifocal ended
            strs = [s, s ++ ".", s ++ "." ++ t, s ++ "." ++ t ++ "."]
        in map (printed cloned) strs === map (printed ended) strs
          .&&. map (parsed cloned) strs === map (parsed ended) strs
    prop "clones inRange, printing & parsing as it does" $
      \(s :: String) -> forAll (choose (0, 4)) $ \lo -> forAll (choose (0, 4)) $ \hi ->
        let range :: Varifocal' String Char
            range = inRange lo (Just hi)
        in printed (cloneVarifocal range) s === printed range s
          .&&. parsed (cloneVarifocal range) s === parsed range s
  describe "heredocs, by delimited" $ do
    let
      printedH h =
        ($ "") <$> printP (heredocP :: Printor String Maybe Heredoc Heredoc) h
      parsedH = parseP (heredocP :: Parsor String Maybe Heredoc Heredoc)
      line = Prelude.filter (/= '\n') <$> arbitrary
    for_ heredocExamples $ \(h, str) ->
      it ("prints & parses " <> show str) $ do
        printedH h `shouldBe` Just str
        parsedH str `shouldBe` Just (h, "")
    it "doesn't print a body line equal to its tag" $
      printedH (Heredoc "EOF" ["EOF"]) `shouldBe` Nothing
    it "closes at the first line equal to its tag" $
      parsedH "<<A\nb\nA\nrest" `shouldBe` Just (Heredoc "A" ["b"], "rest")
    prop "round-trips any heredoc whose body lines aren't its tag" $
      forAll line $ \tag -> forAll (listOf (line `suchThat` (/= tag))) $ \body ->
        let h = Heredoc tag body
        in (printedH h >>= fmap fst . parsedH) === Just h
  describe "cloneVarifocal of a composite, a Prism then a Varifocal" $ do
    let
      composite :: Varifocal' (Either Int String) Char
      composite = _Right . ended
      printedE :: Varifocal' (Either Int String) Char -> Either Int String -> Maybe String
      printedE v e =
        ($ "") <$> printP (contextuallyT v (anyToken :: Printor String Maybe Char Char)) e
      parsedE :: Varifocal' (Either Int String) Char -> String -> Maybe (Either Int String, String)
      parsedE v = parseP (contextuallyT v (anyToken :: Parsor String Maybe Char Char))
    prop "prints & parses as the composite does" $
      forAll plain $ \s -> \(n :: Int) ->
        let es = [Left n, Right s, Right (s ++ ".")]
        in map (printedE (cloneVarifocal composite)) es === map (printedE composite) es
          .&&. parsedE (cloneVarifocal composite) (s ++ ".") === parsedE composite (s ++ ".")
  describe "contextually, in a CtxGrammar" $ do
    for_ heredocExamples $ \(h, str) ->
      it ("parses, prints & parsecs " <> show str <> " as heredocP does") $ do
        [x | (x, "") <- parseG heredocG str] `shouldBe` [h]
        [pr "" | pr <- printG heredocG h] `shouldBe` [str]
        parsecResult (parsecG heredocG str) `shouldBe` Just h
        parsecResult (unparsecG heredocG h "") `shouldBe` Just h
    it "doesn't print a body line equal to its tag" $
      [pr "" | pr <- printG heredocG (Heredoc "EOF" ["EOF"])] `shouldBe` []
    it "backtracks by Parsector, closing at the first line equal to its tag" $
      parsecResult (parsecG heredocG "<<A\nb\nA\n") `shouldBe` Just (Heredoc "A" ["b"])
  describe "Bifocal ⊂ Varifocal" $
    prop "a Prismoid applies contextuallyT as by >?*" $ \(s :: String) ->
      parsed (atLeast 1) s
        === parseP (atLeast 1 >?* (anyToken :: Parsor String Maybe Char Char)) s
      .&&. printed (atLeast 1) s
        === (($ "") <$> printP (atLeast 1 >?* (anyToken :: Printor String Maybe Char Char)) s)
