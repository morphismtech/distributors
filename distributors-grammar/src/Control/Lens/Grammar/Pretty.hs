{- |
Module      : Control.Lens.Grammar.Pretty
Description : grammars laid out, as Wadler-Leijen pretty printers
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable

Grammars which lay themselves out, by the layout combinators of
Wadler, [A prettier printer]
(https://homepages.inf.ed.ac.uk/wadler/papers/prettier/prettier.pdf),
printing a `Doc` of the @prettyprinter@ package, which chooses, by the
page's width, between their flat & broken layouts, & parsing every layout
they print, with any indentation.
-}

module Control.Lens.Grammar.Pretty
  ( -- * PrettyGrammar
    PrettyGrammar (..)
  , PrettyGrammatical
  , prettyG
  , layoutG
  , LayoutStyle (..)
    -- * Layout
  , Lined (..)
  , LaidOut (..)
  , lineP
  , lineP'
  , softlineP
    -- * Prettor
  , Prettor (..)
  ) where

import Control.Applicative
import Control.Lens
import Control.Lens.Grammar.BackusNaur
import Control.Lens.Grammar.RegEx
import Control.Lens.Grammar.Symbol
import Control.Lens.Grammar.Token
import Data.List (intersperse)
import Data.Monoid.Disjunctive
import Data.Profunctor
import Data.Profunctor.Distributor
import Data.Profunctor.Grammar
import Data.Profunctor.Monoidal
import Data.Profunctor.Monoidal.Cocartesian
import Data.String (IsString (..))
import Data.Void (absurd)
import GHC.Exts (Constraint, IsList, Item)
import Prettyprinter
  ( Doc, LayoutOptions, align, flatAlt, group, hardline, layoutCompact
  , layoutPretty, layoutSmart, nest )
import Prettyprinter.Render.String (renderString)
import Witherable (Filterable)

{- | A type's grammar, laid out by `Lined` & `LaidOut` combinators. -}
class PrettyGrammar a where
  prettyGrammar :: PrettyGrammatical p => p a a

{- | The `Grammatical` interpreters of layout, `Lined` & `LaidOut`. -}
type PrettyGrammatical p =
  ( Grammatical Char p
  , forall x y. (x ~ (), y ~ ()) => Lined (p x y)
  , forall x y. LaidOut (p x y)
  , forall x y. (x ~ (), y ~ ()) => IsString (p x y)
  ) :: Constraint

{- | A type's `PrettyGrammar`, printed to a `Doc`, if it prints. -}
prettyG :: PrettyGrammar a => a -> Maybe (Doc ann)
prettyG = fmap snd . runPrettor prettyGrammar

{- | A layout style of a `Doc`, as @prettyprinter@ lays them out. -}
data LayoutStyle
  = PrettyLayout LayoutOptions
  -- ^ by `layoutPretty`, fitting the rest of a line
  | SmartLayout LayoutOptions
  -- ^ by `layoutSmart`, fitting more than the rest of a line
  | CompactLayout
  -- ^ by `layoutCompact`, broken & unindented

{- | A type's `PrettyGrammar`, printed in a `LayoutStyle`, if it prints. -}
layoutG :: PrettyGrammar a => LayoutStyle -> a -> Maybe String
layoutG style a = renderString . laidOut <$> (prettyG a :: Maybe (Doc ()))
  where
    laidOut = case style of
      PrettyLayout opts -> layoutPretty opts
      SmartLayout opts -> layoutSmart opts
      CompactLayout -> layoutCompact

{- | Grammars with a hard line break. -}
class Lined p where
  {- | A newline, which no flat layout removes. -}
  hardlineP :: p

{- | Grammars laid out by Wadler-Leijen layout combinators,
choosing between flat & broken layouts.

> prop> nestP 0 = id
> prop> nestP i . nestP j = nestP (i + j)
-}
class LaidOut p where
  {- | A broken layout, by default, & a flat one, where it's grouped flat. -}
  flatAltP :: p -> p -> p
  {- | Indented further after its line breaks. -}
  nestP :: Int -> p -> p
  {- | Flat, where it fits. -}
  groupP :: p -> p
  {- | Indented to the current column after its line breaks. -}
  alignP :: p -> p

{- | A line break, or a space, where it's grouped flat. -}
lineP :: (Lined p, LaidOut p, IsString p) => p
lineP = flatAltP hardlineP (fromString " ")

{- | A line break, or nothing, where it's grouped flat. -}
lineP' :: (Lined p, LaidOut p, IsString p) => p
lineP' = flatAltP hardlineP (fromString "")

{- | A space, or a line break, where it doesn't fit. -}
softlineP :: (Lined p, LaidOut p, IsString p) => p
softlineP = groupP lineP

-- Doc instances --

instance Lined (Doc ann) where
  hardlineP = hardline
instance LaidOut (Doc ann) where
  flatAltP = flatAlt
  nestP = nest
  groupP = group
  alignP = align

-- RegEx & Bnf instances, the languages of every layout --

-- | A newline, then any indentation.
instance Lined (RegEx Char) where
  hardlineP = terminal "\n" <> starK (token ' ')
-- | Either layout, any indentation.
instance Categorized token => LaidOut (RegEx token) where
  flatAltP = (>|<)
  nestP _ = id
  groupP = id
  alignP = id
instance (Ord rule, Lined rule) => Lined (Bnf rule) where
  hardlineP = liftBnf0 hardlineP
instance (Ord rule, LaidOut rule) => LaidOut (Bnf rule) where
  flatAltP = liftBnf2 flatAltP
  nestP n = liftBnf1 (nestP n)
  groupP = liftBnf1 groupP
  alignP = liftBnf1 alignP

-- Grammor instances --

instance Lined k => Lined (Grammor k a b) where
  hardlineP = Grammor hardlineP
instance LaidOut k => LaidOut (Grammor k a b) where
  flatAltP (Grammor x) (Grammor y) = Grammor (flatAltP x y)
  nestP n = Grammor . nestP n . runGrammor
  groupP = Grammor . groupP . runGrammor
  alignP = Grammor . alignP . runGrammor

-- Parsor instances, parsing every layout --

-- | A newline, then any indentation, unparsing none.
instance
  ( Char ~ Item s, IsList s
  , Cons s s Char Char, Snoc s s Char Char
  , Filterable m, Alternative m, Monad m
  ) => Lined (Parsor s m () ()) where
    hardlineP = newline >* dimap (const "") (const ()) (manyP space)
      where
        newline = terminal "\n" :: Parsor s m () ()
        space = token ' ' :: Parsor s m Char Char
-- | Either layout, any indentation.
instance (Alternative m, Monad m) => LaidOut (Parsor s m a b) where
  flatAltP = (>|<)
  nestP _ = id
  groupP = id
  alignP = id

{- | t'Prettor' is a printer `Profunctor` into a `Monoid`, like a `Doc`,
whose `Lined` & `LaidOut` methods it lifts. -}
newtype Prettor w f a b = Prettor {runPrettor :: a -> f (b, w)}

-- The text of a string, its newlines hard.
linedString :: (IsString w, Lined w, Monoid w) => String -> w
linedString = mconcat . intersperse hardlineP . map fromString . splitLines
  where
    splitLines str = case break (== '\n') str of
      (ln, _ : rest) -> ln : splitLines rest
      (ln, []) -> [ln]

-- Prettor instances
instance Functor f => Functor (Prettor w f a) where
  fmap f (Prettor p) = Prettor (fmap (first' f) . p)
instance Functor f => Profunctor (Prettor w f) where
  dimap f g (Prettor p) = Prettor (fmap (first' g) . p . f)
instance (Monoid w, Applicative f) => Applicative (Prettor w f a) where
  pure b = Prettor (\_ -> pure (b, mempty))
  Prettor f <*> Prettor x = Prettor $ \c ->
    liftA2 (\(g, v) (a, w) -> (g a, v <> w)) (f c) (x c)
instance (Monoid w, Alternative f) => Alternative (Prettor w f a) where
  empty = Prettor (const empty)
  Prettor p <|> Prettor q = Prettor (\a -> p a <|> q a)
instance Functor f => CocartesianMonoidal (Prettor w f) where
  zeroP = Prettor absurd
  Prettor p >+< Prettor q = Prettor $
    either (fmap (first' Left) . p) (fmap (first' Right) . q)
{- | `manyP` & `optionalP` print their elements in turn. -}
instance (Monoid w, Applicative f) => Distributor (Prettor w f) where
  manyP (Prettor p) = Prettor $ \as ->
    (\printed -> (map fst printed, foldMap snd printed)) <$> traverse p as
  optionalP (Prettor p) = Prettor $ \case
    Nothing -> pure (Nothing, mempty)
    Just a -> first' Just <$> p a
instance (Monoid w, Alternative f) => DisjunctiveMonoid (Prettor w f a b)
instance (Monoid w, Alternative f) => CocartesianChoice (Prettor w f) where
  alternate = \case
    Left (Prettor p) -> Prettor $
      either (fmap (first' Left) . p) (const empty)
    Right (Prettor p) -> Prettor $
      either (const empty) (fmap (first' Right) . p)
instance (Monoid w, Alternative f) => Alternator (Prettor w f) where
  optionP def p = pureP def <|> p
instance (Monoid w, Alternative f) => Choice (Prettor w f) where
  left' = alternate . Left
  right' = alternate . Right
instance (IsString w, Lined w, Monoid w, Alternative f)
  => Tokenized Char (Prettor w f Char Char) where
    anyToken = Prettor (\c -> pure (c, linedString [c]))
    token t = tokenClass (token t)
    oneOf ts = tokenClass (oneOf ts)
    notOneOf ts = tokenClass (notOneOf ts)
    asIn cat = tokenClass (asIn cat)
    notAsIn cat = tokenClass (notAsIn cat)
instance (IsString w, Lined w, Monoid w, Alternative f)
  => TokenAlgebra Char (Prettor w f Char Char) where
    -- | The test is made once, rather than for each token.
    tokenClass test = matches `seq` Prettor (\c ->
      if matches c then pure (c, linedString [c]) else empty)
      where
        matches :: Char -> Bool
        matches = tokenClass test
instance (IsString w, Lined w, Monoid w, Applicative f)
  => TerminalSymbol Char (Prettor w f () ()) where
    terminal str = Prettor (\_ -> pure ((), printed))
      where
        printed = linedString str
instance (IsString w, Lined w, Monoid w, Applicative f)
  => IsString (Prettor w f () ()) where
    fromString = terminal
instance Ruled (Prettor w f a b)
instance BackusNaurForm (Prettor w f a b)
instance Tried (Prettor w f a b)
instance (Lined w, Applicative f) => Lined (Prettor w f () ()) where
  hardlineP = Prettor (\_ -> pure ((), hardlineP))
{- | Both layouts print a value, the layout of their prints chosen. -}
instance (LaidOut w, Applicative f) => LaidOut (Prettor w f a b) where
  flatAltP (Prettor p) (Prettor q) = Prettor $ \a ->
    liftA2 (\(b, v) (_, w) -> (b, flatAltP v w)) (p a) (q a)
  nestP n (Prettor p) = Prettor (fmap (fmap (nestP n)) . p)
  groupP (Prettor p) = Prettor (fmap (fmap groupP) . p)
  alignP (Prettor p) = Prettor (fmap (fmap alignP) . p)
