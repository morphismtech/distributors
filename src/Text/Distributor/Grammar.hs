module Text.Distributor.Grammar
  ( Terminal (token, token1, tokens), satisfies
  , NonTerminal (recNonTerminal), nonTerminal
  , NT (NT, runNT), FixNT (fixNT)
  , Grammar (Grammar), Production (..)
  , Parser (Parser), runParser
  , Printer (Printer), runPrinter
  , Linter (Linter), runLinter
  ) where

import Control.Applicative
import Control.Category
import Control.Lens
import Control.Lens.PartialIso
import Control.Lens.Stream
import Control.Monad
import Control.Monad.Fix
import Data.Bifunctor.Joker
import Data.Coerce
import Data.Function hiding ((.))
import Data.List (nub)
import Data.Distributor
import Data.Profunctor
import GHC.Exts
import GHC.OverloadedLabels
import GHC.TypeLits
import Prelude hiding ((.),id)
import Text.ParserCombinators.ReadP
import Witherable

class Terminal c p | p -> c where
  token :: p c c
  token1 :: c -> p () ()
  default token1 :: (Eq c, Cochoice p) => c -> p () ()
  token1 c = only c >?$< token
  tokens :: SimpleStream s c => s -> p () ()
  default tokens :: (Monoidal p, SimpleStream s c) => s -> p () ()
  tokens s = case view _Stream s of
    Left () -> oneP
    Right (a,t) -> token1 a >* tokens t

satisfies :: (Terminal c p, Choice p, Cochoice p) => (c -> Bool) -> p c c
satisfies f = _Guard f >?$?< token

class NonTerminal p where
  recNonTerminal :: String -> (p -> p) -> p
  recNonTerminal _ = fix

nonTerminal :: NonTerminal p => String -> p -> p
nonTerminal symbol p = recNonTerminal symbol (const p)

data NT (s :: [Symbol]) a where
  NT :: FixNT s a => {runNT :: a} -> NT s a
instance ('[s0] ~ s1, a0 ~ a1, KnownSymbol s0, NonTerminal a1)
  => IsLabel s0 (a0 -> NT s1 a1) where fromLabel = NT
instance Functor (NT '[]) where
  fmap f (NT a) = NT (f a)
instance Applicative (NT '[]) where
  pure = NT
  NT f <*> NT a = NT (f a)
instance Monad (NT '[]) where
  return = pure
  NT a >>= f = f a
instance MonadFix (NT '[]) where
  mfix f = NT (fix (runNT . f))

class FixNT (s :: [Symbol]) p where
  fixNT :: (p -> p) -> p
instance FixNT '[] p where
  fixNT = fix
instance
  ( KnownSymbol s, NonTerminal p
  ) => FixNT '[s] p where
    fixNT = recNonTerminal (symbolVal' @s proxy#)
instance
  ( KnownSymbol s0, NonTerminal p0
  , KnownSymbol s1, NonTerminal p1
  ) => FixNT '[s0,s1] (p0,p1) where
    fixNT f =
      let
        ~(p0,p1) =
            ( fixNT @'[s0] @p0 (\q -> view _1 (f (q,p1)))
            , fixNT @'[s1] @p1 (\q -> view _2 (f (p0,q)))
            )
      in (p0,p1)
instance
  ( KnownSymbol s0, NonTerminal p0
  , KnownSymbol s1, NonTerminal p1
  , KnownSymbol s2, NonTerminal p2
  ) => FixNT '[s0,s1,s2] (p0,p1,p2) where
    fixNT f =
      let
        ~(p0,p1,p2) =
            ( fixNT @'[s0] @p0 (\q -> view _1 (f (q,p1,p2)))
            , fixNT @'[s1] @p1 (\q -> view _2 (f (p0,q,p2)))
            , fixNT @'[s2] @p2 (\q -> view _3 (f (p0,p1,q)))
            )
      in (p0,p1,p2)

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
  deriving (Eq, Ord, Read, Show)

data Grammar a b = Grammar [(String, Production)] Production
  deriving (Eq, Ord, Read, Show)
type Prods = [(String, Production)]
mergeProds :: Prods -> Prods -> Prods
mergeProds x y = nub (x ++ y)
instance Functor (Grammar a) where
  fmap = rmap
instance Applicative (Grammar a) where
  pure = pureP
  (<*>) = apP
instance Filterable (Grammar a) where
  mapMaybe = mapMaybeP
instance Alternative (Grammar a) where
  empty = Grammar [] ProdZero
  Grammar prods1 ProdZero <|> Grammar prods2 prod =
    Grammar (mergeProds prods1 prods2) prod
  Grammar prods1 prod <|> Grammar prods2 ProdZero =
    Grammar (mergeProds prods1 prods2) prod
  Grammar prods1 prod1 <|> Grammar prods2 prod2 =
    Grammar (mergeProds prods1 prods2) (ProdPlus prod1 prod2)
  many (Grammar prods prod) = Grammar prods (ProdSev prod)
  some (Grammar prods prod) = Grammar prods (ProdSev1 prod)
instance Profunctor Grammar where
  dimap _ _ = coerce
instance Monoidal Grammar where
  oneP = Grammar [] (ProdString "")
  Grammar prods1 (ProdString "") >*< Grammar prods2 prod =
    Grammar (mergeProds prods1 prods2) prod
  Grammar prods1 prod >*< Grammar prods2 (ProdString "") =
    Grammar (mergeProds prods1 prods2) prod
  Grammar prods1 prod1 >*< Grammar prods2 prod2 =
    Grammar (mergeProds prods1 prods2) (ProdTimes prod1 prod2)
instance Distributor Grammar where
  zeroP = Grammar [] ProdZero
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

newtype Parser f a b = Parser {runParser :: f b}
  deriving
    ( Profunctor
    , Choice
    , Monoidal
    , Distributor
    ) via Joker f
  deriving Functor via Joker f a
instance Applicative f => Applicative (Parser f a) where
  pure = pureP
  (<*>) = apP
instance Alternative f => Alternative (Parser f a) where
  empty = Parser empty
  Parser x <|> Parser y = Parser (x <|> y)
instance MonadPlus f => Filterable (Parser f a) where
  mapMaybe f (Parser x) =
    Parser (maybe mzero return . f =<< x)
instance MonadPlus f => Cochoice (Parser f) where
  unleft (Parser f) =
    Parser (either return (const mzero) =<< f)
  unright (Parser f) =
    Parser (either (const mzero) return =<< f)
instance Terminal Char (Parser ReadP) where
  token = Parser get
instance NonTerminal (Parser ReadP a b)

newtype Printer s a b = Printer (a -> s)
  deriving
    ( Profunctor
    , Choice
    , Cochoice
    , Monoidal
    , Distributor
    ) via Forget s
  deriving
    ( Functor
    ) via Forget s a
instance Monoid s => Applicative (Printer s a) where
  pure = pureP
  (<*>) = apP
instance Filterable (Printer s a) where
  mapMaybe _ (Printer x) = Printer x
instance (Eq c, SimpleStream s c)
  => Terminal c (Printer s) where
    token = Printer (`cons` nil)
instance NonTerminal (Printer s a b)

runPrinter :: Printer s a b -> a -> s
runPrinter (Printer f) x = f x

newtype Linter f s a b = Linter {runLinter :: a -> f s}
instance Functor (Linter f s a) where
  fmap _ (Linter f) = Linter f
instance Profunctor (Linter f s) where
  dimap g _ (Linter linter) = Linter (linter . g)
instance (Applicative f, Monoid s) => Applicative (Linter f s a) where
  pure _ = Linter (\_ -> pure mempty)
  Linter l <*> Linter r = Linter $ \a -> liftA2 (<>) (l a) (r a)
instance (Alternative f, Monoid s) => Alternative (Linter f s a) where
  empty = Linter (\_ -> empty)
  Linter l <|> Linter r = Linter $ \a -> l a <|> r a
instance (Applicative f, Filterable f) => Filterable (Linter f s a) where
  mapMaybe = mapMaybeP
instance (Applicative f, Monoid s) => Monoidal (Linter f s)
instance Cochoice (Linter f s) where
  unleft (Linter linter) = Linter $ linter . Left
  unright (Linter linter) = Linter $ linter . Right
instance (Applicative f, Filterable f) => Choice (Linter f s) where
  left' (Linter linter) = Linter $
    either linter (\_ -> catMaybes (pure Nothing))
  right' (Linter linter) = Linter $
    either (\_ -> catMaybes (pure Nothing)) linter
instance (Alternative f, Filterable f, Monoid s) => Distributor (Linter f s)
instance (Alternative f, Filterable f, Eq c, SimpleStream s c)
  => Terminal c (Linter f s) where
    token = Linter (pure . (`cons` nil))
instance NonTerminal (Linter f s a b)
