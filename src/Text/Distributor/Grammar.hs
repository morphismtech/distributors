module Text.Distributor.Grammar
  ( Grammatical (grammar), gGrammar, gReadP, gPrint, gString
  , Terminal (token, token1, tokens), satisfies
  , NonTerminal (recNonTerminal), nonTerminal
  , NT (NT), runNT
  , Grammar (Grammar), Production (..)
  , Parser (Parser), runParser
  , Printer (Printer), runPrinter
  , Linter (Linter), runLinter
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.PartialIso
import Control.Lens.Stream
import Control.Monad
import Data.Bifunctor.Joker
import Data.Coerce
import Data.Function
import Data.Kind
import Data.List (nub)
import Data.Distributor
import Data.Profunctor
import GHC.OverloadedLabels
import GHC.TypeLits
import Text.ParserCombinators.ReadP
import Witherable

class Grammatical c a where
  grammar :: (Terminal c p, forall x y. NonTerminal (p x y)) => p a a

gGrammar :: Grammatical Char a => Grammar a a
gGrammar = grammar

gReadP :: Grammatical Char a => ReadP a
gReadP = runParser grammar

gPrint :: (Eq c, Grammatical c a, SimpleStream s c) => a -> s
gPrint = runPrinter grammar

gString :: Grammatical Char a => a -> String
gString = gPrint

class (Eq c, Distributor p, Choice p, Cochoice p)
  => Terminal c p | p -> c where
    token :: p c c
    token1 :: c -> p () ()
    token1 c = only c >?$< token
    tokens :: SimpleStream s c => s -> p () ()
    tokens s =
      let
        emp () = one
        cns (a,t) = token1 a >* tokens t
      in
        either emp cns (view _Stream s)

satisfies :: Terminal c p => (c -> Bool) -> p c c
satisfies f = _Guard f >?$?< token

class NonTerminal p where
  recNonTerminal :: String -> (p -> p) -> p
  recNonTerminal _ = fix

nonTerminal :: NonTerminal p => String -> p -> p
nonTerminal symbol p = recNonTerminal symbol (const p)

type NT :: Symbol -> Type -> Type
newtype NT s a = NT a
  deriving
    ( Functor
    , Applicative
    , Monad
    ) via Identity
instance s0 ~ s1 => IsLabel s0 (a -> NT s1 a) where
  fromLabel = NT

runNT :: (forall s. NT s a) -> a
runNT (NT a) = a

data Production
  = ProdToken
  | ProdChar Char
  | ProdString String
  | ProdNonTerminal String
  | ProdZero
  | ProdTimes Production Production
  | ProdPlus Production Production
  | ProdSev Production
  | ProdSev1 Production
  | ProdPoss Production
  | ProdCase Production
  | ProdCocase Production
  deriving Eq

data Grammar a b = Grammar [(String, Production)] Production
instance Profunctor Grammar where
  dimap _ _ = coerce
type Prods = [(String, Production)]
mergeProds :: Prods -> Prods -> Prods
mergeProds x y = nub (x ++ y)
instance Monoidal Grammar where
  one = Grammar [] (ProdString "")
  Grammar prods1 (ProdString "") >*< Grammar prods2 prod =
    Grammar (mergeProds prods1 prods2) prod
  Grammar prods1 prod >*< Grammar prods2 (ProdString "") =
    Grammar (mergeProds prods1 prods2) prod
  Grammar prods1 prod1 >*< Grammar prods2 prod2 =
    Grammar (mergeProds prods1 prods2) (ProdTimes prod1 prod2)
instance Distributor Grammar where
  zero = Grammar [] ProdZero
  Grammar prods1 ProdZero >+< Grammar prods2 prod =
    Grammar (mergeProds prods1 prods2) prod
  Grammar prods1 prod >+< Grammar prods2 ProdZero =
    Grammar (mergeProds prods1 prods2) prod
  Grammar prods1 prod1 >+< Grammar prods2 prod2 =
    Grammar (mergeProds prods1 prods2) (ProdPlus prod1 prod2)
  several (Grammar prods prod) = Grammar prods (ProdSev prod)
  severalMore (Grammar prods prod) = Grammar prods (ProdSev1 prod)
  possibly (Grammar prods prod) = Grammar prods (ProdPoss prod)
instance Choice Grammar where
  left' (Grammar prods prod) = Grammar prods (ProdCase prod)
  right' (Grammar prods prod) = Grammar prods (ProdCase prod)
instance Cochoice Grammar where
  unleft (Grammar prods prod) = Grammar prods (ProdCocase prod)
  unright (Grammar prods prod) = Grammar prods (ProdCocase prod)
instance Terminal Char Grammar where
  token = Grammar [] ProdToken
  token1 chr = Grammar [] (ProdChar chr)
  tokens str = Grammar [] (ProdString (convertStream str))
instance NonTerminal (Grammar a b) where
  recNonTerminal symbol f =
    let Grammar prods prod = f (Grammar [] (ProdNonTerminal symbol))
    in Grammar (prods ++ [(symbol, prod)]) (ProdNonTerminal symbol)

newtype Parser f a b = Parser (Joker f a b)
  deriving newtype
    ( Functor
    , Profunctor
    , Choice
    , Monoidal
    , Distributor
    )
instance Applicative f => Applicative (Parser f a) where
  pure = pureP
  (<*>) = apP
instance Alternative f => Alternative (Parser f a) where
  empty = Parser (Joker empty)
  Parser (Joker x) <|> Parser (Joker y) = Parser (Joker (x <|> y))
instance MonadPlus f => Filterable (Parser f a) where
  mapMaybe f (Parser (Joker x)) =
    Parser (Joker (maybe mzero return . f =<< x))
instance MonadPlus f => Cochoice (Parser f) where
  unleft (Parser (Joker f)) =
    Parser (Joker (either return (const mzero) =<< f))
  unright (Parser (Joker f)) =
    Parser (Joker (either (const mzero) return =<< f))
instance Terminal Char (Parser ReadP) where
  token = Parser (Joker get)
instance NonTerminal (Parser f a b)

runParser :: Parser f a b -> f b
runParser (Parser (Joker f)) = f

newtype Printer r a b = Printer (Forget r a b)
  deriving newtype
    ( Functor
    , Profunctor
    , Choice
    , Cochoice
    , Monoidal
    , Distributor
    )
instance Monoid r => Applicative (Printer r a) where
  pure = Printer . pureP
  Printer x <*> Printer y = Printer $ apP x y
instance Monoid r => Alternative (Printer r a) where
  empty = Printer emptyP
  Printer x <|> Printer y = Printer $ altL x y
instance Filterable (Printer r a) where
  mapMaybe _ (Printer (Forget x)) = Printer (Forget x)
instance (Eq c, SimpleStream s c)
  => Terminal c (Printer s) where
    token = Printer (Forget (`cons` nil))
instance NonTerminal (Printer r a b)

runPrinter :: Printer r a b -> a -> r
runPrinter (Printer (Forget f)) x = f x

newtype Linter f r a b = Linter {runLinter :: a -> f r}
instance Functor (Linter f r a) where
  fmap _ (Linter f) = Linter f
instance Profunctor (Linter f r) where
  dimap g _ (Linter linter) = Linter (linter . g)
instance (Applicative f, Monoid r) => Applicative (Linter f r a) where
  pure _ = Linter (\_ -> pure mempty)
  Linter l <*> Linter r = Linter $ \a -> liftA2 (<>) (l a) (r a)
instance (Alternative f, Monoid r) => Alternative (Linter f r a) where
  empty = Linter (\_ -> empty)
  Linter l <|> Linter r = Linter $ \a -> l a <|> r a
instance (Applicative f, Filterable f) => Filterable (Linter f r a) where
  mapMaybe = mapMaybeP
instance (Applicative f, Monoid r) => Monoidal (Linter f r)
instance Cochoice (Linter f r) where
  unleft (Linter linter) = Linter $ linter . Left
  unright (Linter linter) = Linter $ linter . Right
instance (Applicative f, Filterable f) => Choice (Linter f r) where
  left' (Linter linter) = Linter $
    either linter (\_ -> catMaybes (pure Nothing))
  right' (Linter linter) = Linter $
    either (\_ -> catMaybes (pure Nothing)) linter
instance (Alternative f, Filterable f, Monoid r) => Distributor (Linter f r)
