module Properties.Pretty (prettyProperties) where

import Control.Lens.Grammar hiding (List)
import Data.Foldable (for_)
import Prettyprinter (LayoutOptions (..), PageWidth (..))
import Examples.SExpr
import Test.Hspec

prettyProperties :: Spec
prettyProperties = do
  let
    width n = LayoutOptions (AvailablePerLine n 1)
    styles =
      [ PrettyLayout (width 80), PrettyLayout (width 10)
      , SmartLayout (width 10), CompactLayout ]
    parsed = parseP (prettyGrammar :: Parsor String Maybe SExpr SExpr)
    bnf = runGrammor (prettyGrammar :: Grammor (Bnf (RegEx Char)) SExpr SExpr)
    define = List
      [ Atom "define", List [Atom "square", Atom "x"]
      , List [Atom "*", Atom "x", Atom "x"] ]
  it "prints flat where it fits" $
    for_ sexprExamples $ \(sexpr, str) ->
      layoutG (PrettyLayout (width 80)) sexpr `shouldBe` Just str
  it "breaks lines where it doesn't fit, aligned" $
    layoutG (PrettyLayout (width 20)) define
      `shouldBe` Just "(define\n (square x)\n (* x x))"
  it "parses what it prints, in every layout style" $
    for_ sexprExamples $ \(sexpr, _) -> for_ styles $ \style ->
      (layoutG style sexpr >>= parsed) `shouldBe` Just (sexpr, "")
  it "parses any indentation" $
    parsed "(define\n(square x)\n      (* x x))" `shouldBe` Just (define, "")
  it "describes every layout it prints, as a Bnf" $
    for_ sexprExamples $ \(sexpr, _) -> for_ styles $ \style ->
      fmap (=~ bnf) (layoutG style sexpr) `shouldBe` Just True
