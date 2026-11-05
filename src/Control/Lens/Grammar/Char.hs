{-# LANGUAGE OverloadedStrings, RequiredTypeArguments #-}

{-|
Module      : Control.Lens.Grammar.Char
Description : grammars of Haskell's Read & Show syntax
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable

`Textual` types have @LL(1)@ grammars of Haskell's `Read` & `Show` syntax,
which print as `show` does & parse what `read` does, written against an
interface, `CharGrammatical`, separate from their interpreters, which run
through `Parsector`, `Parsor`, `Printor` & `Grammor`, reading the
precedence of their context.

The exception is redundant parentheses around a value whose own form
starts with a parenthesis, like @((1,2))@, which `read` accepts.

Textual grammars are written with lexemes, which end by consuming
the whitespace after them, & check that what follows can't continue
them, as @read@'s lexer would, so that @Just1@ isn't @Just 1@.
Parentheses are written with `charGroup`, the generator of Dyck words,
& sub-terms with `charAt`, which adds the parentheses that their context
requires or allows, analysing the sub-term's grammar to keep it @LL(1)@.
-}

module Control.Lens.Grammar.Char
  ( -- * Textual
    Textual (..)
  , Textually (..)
    -- * Runners
  , charShowsPrec
  , charErrorShowsPrec
  , charReadsPrec
  , charParsePrec
  , charUnparsePrec
  , charParsecPrec
  , charUnparsecPrec
  , charGrammarPrec
  , TextualError (..)
    -- * CharGrammatical
  , CharGrammatical (..)
  , Prec
  , CharName (..)
  , charPrec
  , charTerm
  , charOperandTerm
  , charPunct
  ) where

import Control.Applicative (ZipList (..))
import Control.Lens hiding (Empty)
import Control.Lens.Grammar
import Control.Monad
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Reader (ReaderT, ask, local, runReaderT)
import Control.Monad.Trans.State.Strict
import Data.ByteString qualified as ByteString
import Data.ByteString.Char8 qualified as Char8
import Data.ByteString.Lazy qualified as LByteString
import Data.ByteString.Lazy.Char8 qualified as LChar8
import Data.Char (chr, isAlpha, isDigit, ord)
import Data.Complex (Complex)
import Data.Fixed (Fixed, HasResolution)
import Data.Foldable (toList)
import Data.Function (on)
import Data.Functor.Compose (Compose (..))
import Data.Functor.Product qualified as Functor
import Data.Functor.Sum qualified as Functor
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HashMap
import Data.HashSet (HashSet)
import Data.HashSet qualified as HashSet
import Data.Hashable (Hashable)
import Data.Int (Int8, Int16, Int32, Int64)
import Data.IntMap (IntMap)
import Data.IntMap qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.Kind (Constraint)
import Data.List (groupBy, sortOn)
import Data.List.NonEmpty (NonEmpty)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe hiding (mapMaybe)
import Data.Monoid qualified as Monoid
import Data.Ord (Down (..))
import Data.Profunctor
import Data.Proxy (Proxy)
import Data.Ratio (Ratio, denominator, numerator, (%))
import Data.Semigroup qualified as Semigroup
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.Set (Set)
import Data.Set qualified as Set
import Data.String (IsString (..))
import Data.Text qualified as Text
import Data.Text.Lazy qualified as LText
import Data.Text.Short qualified as ShortText
import Data.Tree (Tree)
import Data.Tuple (Solo)
import Data.Vector qualified as Vector
import Data.Version (Version)
import Data.Void (Void)
import Data.Word (Word8, Word16, Word32, Word64)
import Foreign.C.Types
import GHC.Exts (Item)
import GHC.Generics qualified as GHC
import Numeric.Natural (Natural)
import System.Exit (ExitCode)
import System.IO (BufferMode (..), IOMode (..), SeekMode (..))
import Text.ParserCombinators.ReadPrec (Prec, readS_to_Prec)
import Text.Read (Read (..))
import Type.Reflection (Typeable, typeRep)

{-
class
  ( Lexical Char p
  , Alternator p
  , Filtrator p
  , forall x y. BackusNaurForm (p x y)
  , forall x y. (x ~ (), y ~ ()) => IsString (p x y)
  ) => CharGrammatical p where
    charPrec :: Prec -> p a a -> p a a

class Textual a where charGrammar :: CharGrammatical p => p a a

charErrorShowsPrec :: Textual a => Prec -> a -> Either TextualError ShowS
charReadsPrec :: Textual a => Prec -> ReadS a
charParsecPrec :: (Textual a, ..) => Prec -> string -> ParsecState string a
charUnparsecPrec :: (Textual a, ..) => Prec -> a -> ParsecString string a
charGrammarPrec :: Prec -> forall a. (a :: Type) -> Textual a => RegBnf a
charParsePrec :: (Textual a, ..) => Prec -> string -> m (a, string)
charUnparsePrec :: (Textual a, ..) => Prec -> a -> string -> m string

-- Interpreters should run through Parsector, Parsor, Printor & Grammor;
-- to exercise these types in order to improve their performance.
-- Instances should maintain the LL(1) invariant - unless that's incompatible with precision/parens...
-}

-- CharGrammatical --

-- | The base classes of a `CharGrammatical` interpreter.
type CharSyntactic p =
  ( Lexical Char p
  , Alternator p
  , Filtrator p
  , forall x y. BackusNaurForm (p x y)
  , forall x y. (x ~ (), y ~ ()) => IsString (p x y)
  ) :: Constraint

{- | The sorts of lexemes, which end differently: a word mayn't be followed
by a character of a word, nor an operator by a character of an operator,
since @read@'s lexer would continue them.
-}
data Lexeme = Word | Operator
  deriving stock (Eq, Ord, Show, Read, Enum, Bounded)

{- | A constructor's name, with the precedences at which its form
is shown & read, the values it shows, & its form after its name.
-}
data CharName p a = CharName
  { charName :: String
  , charShown :: Prec
  , charRead :: Prec
  , charShows :: a -> Bool
  , charForm :: p a a
  }

{- | `CharGrammatical` interpreters of Haskell's `Read` & `Show` syntax.

Forms have precedences, like `Text.Read.prec` & `showParen`,
& sub-terms have the precedences of their contexts,
like `Text.Read.step` & `Text.Read.reset`.

prop> charPrec n = charPrecs n n
-}
class CharSyntactic p => CharGrammatical p where

  {- | A form, shown in contexts of precedence up to its first,
  & read in contexts of precedence up to its second, so that @-1@ is
  shown as @(-1)@ as an argument, but is read either way. -}
  charPrecs :: Prec {- ^ shown -} -> Prec {- ^ read -} -> p a a -> p a a

  {- | A sub-term in a context of a precedence, parenthesized when its form
  requires it, & optionally otherwise, unless that would be ambiguous,
  because one of its forms starts with a parenthesis itself.
  Its grammar is polymorphic, so that it can be analysed,
  & its rule is named by its type.
  -}
  charAt
    :: Typeable a
    => Prec -> (forall q. CharGrammatical q => q a a) -> p a a

  {- | A sub-term leading a form, like the left operand of an infix
  constructor, parenthesized only when its form requires it, since an
  optional parenthesis would be ambiguous with those of other forms.
  -}
  charOperand
    :: Typeable a
    => Prec -> (forall q. CharGrammatical q => q a a) -> p a a

  {- | Parentheses around a grammar, the generator of Dyck words,
  which distributes over alternatives,

  prop> charGroup (p >+< q) = charGroup p >+< charGroup q
  -}
  charGroup :: p a a -> p a a
  charGroup p = charPunct "(" >* p *< charPunct ")"

  {- | A word, like a constructor's name, which mayn't be followed by
  a character of a word, & then any whitespace. -}
  charWord :: String -> p () ()

  {- | An operator, like an infix constructor's name, which mayn't be
  followed by a character of an operator, & then any whitespace. -}
  charOperator :: String -> p () ()

  -- | A lexeme, like a literal or punctuation, & then any whitespace.
  charLexeme :: p a a -> p a a

  -- | A space, as `show` prints one, which isn't parsed.
  charSpace :: p () ()

  {- | Constructors by name, factored by their names' characters,
  so that they're @LL(1)@ when one name prefixes another. -}
  charNamed :: [CharName p a] -> p a a
  charNamed names = trie
    [ (charName n, charShows n, charWord "" >* charPrecs s r (charForm n))
    | n@CharName {charShown = s, charRead = r} <- names ]

-- | A `Textual` type's grammar as a sub-term, `charAt` a precedence.
charTerm :: forall a p. (Textual a, CharGrammatical p) => Prec -> p a a
charTerm d = charAt d (charGrammar @a)

-- | A `Textual` type's grammar as a leading sub-term, `charOperand`.
charOperandTerm
  :: forall a p. (Textual a, CharGrammatical p) => Prec -> p a a
charOperandTerm d = charOperand d (charGrammar @a)

-- | A form shown & read at a precedence.
charPrec :: CharGrammatical p => Prec -> p a a -> p a a
charPrec n = charPrecs n n

-- | Punctuation, like a comma or a bracket.
charPunct :: CharGrammatical p => String -> p () ()
charPunct str = charLexeme (terminal str)

{- | Factor named forms by their names' characters,
each branch printing the values of its names.
-}
trie :: CharSyntactic p => [(String, a -> Bool, p a a)] -> p a a
trie entries = orP (branches <> leaves)
  where
    branches =
      [ guarded (\a -> any (\(_, test, _) -> test a) group) $
          terminal prefix
          >* trie
            [(drop (length prefix) name, test, g) | (name, test, g) <- group]
      | group <- groupBy ((==) `on` first) (sortOn first named)
      , let prefix = foldr1 common [name | (name, _, _) <- group]
      ]
    named = [entry | entry@(_ : _, _, _) <- entries]
    leaves = [guarded test g | ("", test, g) <- entries]
    first (name, _, _) = take 1 name
    common (x : xs) (y : ys) | x == y = x : common xs ys
    common _ _ = []

-- | Print only the values which pass a test.
guarded :: Choice p => (a -> Bool) -> p a a -> p a a
guarded test = (prism' id (\a -> a <$ guard (test a)) >?)

-- | Parse, but don't print.
parseOnly :: Choice p => p a a -> p a a
parseOnly = guarded (const False)

-- | A whitespace character, as @read@'s lexer has them.
spaceG :: CharSyntactic p => p Char Char
spaceG = tokenClass (oneOf ("\t\n\v\f\r" :: String) >|< asIn Space)

-- | Whitespace, which isn't printed.
spaces :: CharSyntactic p => p () ()
spaces = dimap (const "") (const ()) (manyP spaceG)

-- | The characters which continue a lexeme of a sort.
continuing :: Lexeme -> TokenClass Char
continuing = \case
  Word -> oneOf ("_'" :: String) >|< anyP asIn
    [ UppercaseLetter, LowercaseLetter, TitlecaseLetter, ModifierLetter
    , OtherLetter, DecimalNumber ]
  Operator -> oneOf ("!#$%&*+./<=>?@\\^|-~:" :: String) >|< anyP asIn
    [MathSymbol, CurrencySymbol, ModifierSymbol, OtherSymbol]

-- Textual --

{- | `Textual` types have grammars of Haskell's `Read` & `Show` syntax.

> data Point = Point {x :: Int, y :: Int}
>   deriving stock Generic
>   deriving anyclass Textual
>   deriving (Show, Read) via Textually Point
-}
class Typeable a => Textual a where
  charGrammar :: CharGrammatical p => p a a
  default charGrammar
    :: (GHC.Generic a, GTextual (GHC.Rep a), CharGrammatical p) => p a a
  charGrammar = iso GHC.from GHC.to >~ charForms gforms
  {- | The grammar of a list, like `showList` & `Text.Read.readListPrec`,
  by default in brackets, @[a,b,c]@. -}
  charListGrammar :: CharGrammatical p => p [a] [a]
  charListGrammar = charBrackets

-- | Named & other forms.
charForms :: CharGrammatical p => [Either (CharName p a) (p a a)] -> p a a
charForms forms = orP $
  [charNamed names | not (null names)] <> [g | Right g <- forms]
  where
    names = [n | Left n <- forms]

-- | A list in brackets, @[a,b,c]@.
charBrackets :: forall a p. (Textual a, CharGrammatical p) => p [a] [a]
charBrackets = charPunct "[" >*
  ( _Empty >? charPunct "]"
  >|< _Cons >? charTerm @a 0
    >*< manyP (charPunct "," >* charTerm @a 0)
    *< charPunct "]"
  )

-- | An error printing a value, at a rule.
newtype TextualError = TextualError (ParsecFailure String)
  deriving stock (Eq, Show)

-- | A `Textual` type's grammar at a precedence, after leading whitespace.
grammarAt :: forall a p. (Textual a, CharGrammatical p) => Prec -> p a a
grammarAt d = spaces >* charTerm @a d

-- | `showsPrec`, by `Printor`.
charShowsPrec :: Textual a => Prec -> a -> ShowS
charShowsPrec d a = either (error . show) id (charErrorShowsPrec d a)

{- | `showsPrec`, by `Printor`, or the failure to print, by `Parsector`,
which only a lawless grammar fails to do. -}
charErrorShowsPrec
  :: forall a. Textual a => Prec -> a -> Either TextualError ShowS
charErrorShowsPrec d a =
  case printP (runPreced (grammarAt @a d) 0) a of
    Just printed -> Right printed
    Nothing -> Left (TextualError (parsecFailure (charUnparsecPrec d a)))

-- | `readsPrec`, by `Parsor`.
charReadsPrec :: Textual a => Prec -> ReadS a
charReadsPrec = charParsePrec

{- | Parse, by `Parsor`, returning the rest of the input.
Its input is a `String`, since `Parsor` has `IsString` instances
for both @Parsor s m () ()@ & @Parsor s m s s@,
which overlap for an unknown input type. -}
charParsePrec
  :: forall a m. (Textual a, Alternative m, Monad m, Filterable m)
  => Prec -> String -> m (a, String)
charParsePrec d = parseP (runPreced (grammarAt @a d) 0)

-- | Print, by `Parsor`, after an input.
charUnparsePrec
  :: forall a m. (Textual a, Alternative m, Monad m, Filterable m)
  => Prec -> a -> String -> m String
charUnparsePrec d = unparseP (runPreced (grammarAt @a d) 0)

-- | Parse predictively, by `Parsector`.
charParsecPrec
  :: forall a string. (Textual a, Cons string string Char Char)
  => (Snoc string string Char Char, Item string ~ Char)
  => Prec -> string -> ParsecState string a
charParsecPrec d = parsecP (runPreced (grammarAt @a d) 0)

-- | Print predictively, by `Parsector`.
charUnparsecPrec
  :: forall a string. (Textual a, Cons string string Char Char)
  => (Snoc string string Char Char, Item string ~ Char, AsEmpty string)
  => Prec -> a -> ParsecState string a
charUnparsecPrec d a = unparsecP (runPreced (grammarAt @a d) 0) a Empty

-- | The `RegBnf` of a `Textual` type's grammar at a precedence, by `Grammor`.
charGrammarPrec :: Prec -> forall a -> Textual a => RegBnf
charGrammarPrec d a = definingG (runPreced (grammarAt @a d) 0)

{- | `Show` & `Read` instances, derived from a `Textual` instance.

> data Point = Point {x :: Int, y :: Int}
>   deriving stock Generic
>   deriving anyclass Textual
>   deriving (Show, Read) via Textually Point
-}
newtype Textually a = Textually a

instance Textual a => Show (Textually a) where
  showsPrec d (Textually a) = charShowsPrec d a
  showList as = charShowsPrec 0 (map (\(Textually a) -> a) as)
instance Textual a => Read (Textually a) where
  readPrec = readS_to_Prec (\d -> map (first' Textually) . charReadsPrec d)
  readListPrec = readS_to_Prec $ \d ->
    map (first' (map Textually)) . charReadsPrec d

-- Interpreters --

{- | An interpreter of a `CharGrammatical` grammar, reading the precedence
of its context, through a base interpreter, like `Parsector`.
-}
newtype Preced q a b = Preced {runPreced :: Prec -> q a b}

{- | Base interpreters which can end a lexeme, checking the next character
without consuming it, then skipping whitespace, & print what they don't parse.
-}
class CharPeek q where
  {- | Fail, without consuming, if the next character is of a class,
  & otherwise skip whitespace, which isn't printed. -}
  endLexeme :: TokenClass Char -> q () ()
  -- | Print a string, but parse nothing.
  printOnly :: String -> q () ()

-- | A whitespace character, as @read@'s lexer has them.
spaceClass :: TokenClass Char
spaceClass = oneOf ("\t\n\v\f\r" :: String) >|< asIn Space

instance
  ( Item s ~ Char, Cons s s Char Char, Snoc s s Char Char
  ) => CharPeek (Parsector s) where
    endLexeme cls = Parsector $ \callback query -> callback $
      case parsecResult query of
        Just () -> query
        Nothing -> case uncons (parsecStream query) of
          Just (c, _) | continues c -> query
            { parsecFailure = ParsecFailure (notP cls) []
            , parsecResult = Nothing
            }
          _ -> skip query (parsecStream query)
      where
        continues = tokenClass cls
        isSpace = tokenClass spaceClass
        skip query str = case uncons str of
          Just (c, rest) | isSpace c -> skip query
            { parsecLooked = True
            , parsecFailure = mempty
            , parsecStream = rest
            , parsecOffset = parsecOffset query + 1
            } rest
          _ -> query {parsecResult = Just ()}
    printOnly str = Parsector $ \callback query -> callback $
      case parsecResult query of
        Nothing -> query {parsecResult = Just ()}
        Just () -> query
          { parsecStream = foldl' snoc (parsecStream query) str
          , parsecOffset = parsecOffset query + fromIntegral (length str)
          }
instance
  ( Item s ~ Char, Cons s s Char Char, Snoc s s Char Char, Alternative m
  ) => CharPeek (Parsor s m) where
    endLexeme cls = Parsor $ \mode str -> case mode of
      Nothing -> case uncons str of
        Just (c, _) | tokenClass cls c -> empty
        _ -> pure ((), skip str)
      Just () -> pure ((), str)
      where
        isSpace = tokenClass spaceClass
        skip str = case uncons str of
          Just (c, rest) | isSpace c -> skip rest
          _ -> str
    printOnly printed = Parsor $ \mode str -> case mode of
      Nothing -> pure ((), str)
      Just () -> pure ((), foldl' snoc str printed)
instance (Item s ~ Char, Cons s s Char Char, Applicative m)
  => CharPeek (Printor s m) where
    endLexeme _ = Printor (\_ -> pure ((), id))
    printOnly printed =
      Printor (\_ -> pure ((), \str -> foldr cons str printed))
instance (KleeneStarAlgebra k, TokenAlgebra Char k) => CharPeek (Grammor k) where
  endLexeme _ = Grammor (starK (tokenClass spaceClass))
  printOnly _ = Grammor mempty

instance Profunctor q => Profunctor (Preced q) where
  dimap f g (Preced p) = Preced (dimap f g . p)
instance Functor (q a) => Functor (Preced q a) where
  fmap f (Preced p) = Preced (fmap f . p)
instance Applicative (q a) => Applicative (Preced q a) where
  pure b = Preced (const (pure b))
  liftA2 f (Preced p) (Preced q) = Preced (\d -> liftA2 f (p d) (q d))
instance Alternative (q a) => Alternative (Preced q a) where
  empty = Preced (const empty)
  Preced p <|> Preced q = Preced (\d -> p d <|> q d)
  many (Preced p) = Preced (many . p)
  some (Preced p) = Preced (some . p)
instance Choice q => Choice (Preced q) where
  left' (Preced p) = Preced (left' . p)
  right' (Preced p) = Preced (right' . p)
instance Cochoice q => Cochoice (Preced q) where
  unleft (Preced p) = Preced (unleft . p)
  unright (Preced p) = Preced (unright . p)
instance Filterable (q a) => Filterable (Preced q a) where
  mapMaybe f (Preced p) = Preced (mapMaybe f . p)
instance Filtrator q => Filtrator (Preced q) where
  filtrate (Preced p) =
    (Preced (fst . filtrate . p), Preced (snd . filtrate . p))
instance DisjunctiveMonoid (q a b) => DisjunctiveMonoid (Preced q a b) where
  falseP = Preced (const falseP)
  Preced p >|< Preced q = Preced (\d -> p d >|< q d)
instance CocartesianMonoidal q => CocartesianMonoidal (Preced q) where
  zeroP = Preced (const zeroP)
  Preced p >+< Preced q = Preced (\d -> p d >+< q d)
instance CocartesianChoice q => CocartesianChoice (Preced q) where
  alternate = \case
    Left (Preced p) -> Preced (alternate . Left . p)
    Right (Preced p) -> Preced (alternate . Right . p)
instance Distributor q => Distributor (Preced q) where
  manyP (Preced p) = Preced (manyP . p)
  optionalP (Preced p) = Preced (optionalP . p)
instance Alternator q => Alternator (Preced q) where
  someP (Preced p) = Preced (someP . p)
  optionP def (Preced p) = Preced (optionP def . p)
instance Tokenized Char (q a b) => Tokenized Char (Preced q a b) where
  anyToken = Preced (const anyToken)
  token c = Preced (const (token c))
  oneOf cs = Preced (const (oneOf cs))
  notOneOf cs = Preced (const (notOneOf cs))
  asIn cat = Preced (const (asIn cat))
  notAsIn cat = Preced (const (notAsIn cat))
instance TokenAlgebra Char (q a b) => TokenAlgebra Char (Preced q a b) where
  tokenClass cls = Preced (const (tokenClass cls))
instance TerminalSymbol Char (q a b) => TerminalSymbol Char (Preced q a b) where
  terminal str = Preced (const (terminal str))
instance (x ~ (), y ~ (), IsString (q () ())) => IsString (Preced q x y) where
  fromString str = Preced (const (fromString str))
-- | Rules are named by the precedence of their contexts.
instance BackusNaurForm (q a b) => BackusNaurForm (Preced q a b) where
  rule name (Preced p) = Preced (\d -> rule (precName name d) (p d))
  ruleRec name f = Preced $ \d ->
    ruleRec (precName name d) (\q -> runPreced (f (Preced (const q))) d)

-- | A rule's name in a context of a precedence.
precName :: String -> Prec -> String
precName name d = if d == 0 then name else name <> "@" <> show d

instance (CharSyntactic q, CharPeek q) => CharGrammatical (Preced q) where
  charPrecs shown readAt (Preced p) = Preced $ \d ->
    if d <= shown then p d else if d <= readAt then parseOnly (p d) else falseP
  charAt d g = Preced $ \_ -> subterm False d g
  charOperand d g = Preced $ \_ -> subterm True d g
  charWord name = Preced $ \_ -> terminal name >* endLexeme (continuing Word)
  charOperator name =
    Preced $ \_ -> terminal name >* endLexeme (continuing Operator)
  charLexeme (Preced p) = Preced $ \d -> p d *< endLexeme falseP
  charSpace = Preced (const (printOnly " "))
  charNamed names = Preced $ \d -> trie
    [ (charName n, if d <= s then charShows n else const False, end >* form d)
    | n@CharName {charShown = s, charRead = r} <- names, d <= r
    , let Preced form = charForm n ]
    where
      end = endLexeme (continuing Word)

{- | A sub-term at a precedence, through a base interpreter, with the
parentheses its context requires or allows, decided by its `Shape`.
-}
subterm
  :: forall a q. (Typeable a, CharSyntactic q, CharPeek q)
  => Bool -> Prec -> (forall p. CharGrammatical p => p a a) -> q a a
subterm operand d g =
  rule (precName (show (typeRep @a)) d) $ runPreced g d >|< wrapper
  where
    wrapper
      | parenthesized operand d (shapeOf @a g) =
          runPreced (charGroup (charAt @_ @a 0 g)) 0
      | otherwise = falseP

-- Shapes --

{- | The shape of a form: the precedences it's shown & read at,
& whether it starts with a parenthesis. -}
data FormShape = FormShape Prec Prec Bool

{- | The shape of a grammar's forms, or `Nothing` if it's transparent,
like whitespace, so that a sequence has the shape of its first opaque part,
with the names of the rules being analysed, to stop at recursion.
-}
newtype Shape = Shape (Set String -> Maybe [FormShape])

-- | The shapes of a grammar's forms.
shapeOf
  :: forall a. Typeable a
  => (forall p. CharGrammatical p => p a a) -> [FormShape]
shapeOf g = case g @(Grammor Shape) of
  Grammor (Shape shape) -> fromMaybe [] (shape (Set.singleton name))
  where
    name = show (typeRep @a)

{- | Whether a sub-term is offered parentheses at a precedence:
when some form requires them, or, unless it's an operand, when no form
read at that precedence starts with a parenthesis.
-}
parenthesized :: Bool -> Prec -> [FormShape] -> Bool
parenthesized operand d forms = required || not (operand || ambiguous)
  where
    required = or [shown < d | FormShape shown _ _ <- forms]
    ambiguous = or [grouped | FormShape _ readAt grouped <- forms, d <= readAt]

-- | An atomic form.
atom :: Bool -> Maybe [FormShape]
atom grouped = Just [FormShape 11 11 grouped]

instance Semigroup Shape where
  Shape x <> Shape y = Shape (\names -> maybe (y names) Just (x names))
instance Monoid Shape where
  mempty = Shape (const Nothing)
instance DisjunctiveMonoid Shape where
  falseP = Shape (const (Just []))
  Shape x >|< Shape y = Shape $ \names -> case (x names, y names) of
    (Nothing, b) -> b
    (a, Nothing) -> a
    (Just a, Just b) -> Just (a <> b)
instance KleeneStarAlgebra Shape where
  starK = id
  plusK = id
  optK = id
instance Tokenized Char Shape where
  anyToken = Shape (const (atom True))
  token c = Shape (const (atom (c == '(')))
  oneOf cs = Shape (const (atom ('(' `elem` cs)))
  notOneOf cs = Shape (const (atom ('(' `notElem` cs)))
  asIn _ = Shape (const (atom False))
  notAsIn _ = Shape (const (atom True))
instance TokenAlgebra Char Shape where
  tokenClass cls = Shape (const (atom (tokenClass cls '(')))
instance TerminalSymbol Char Shape where
  terminal = \case
    [] -> mempty
    c : _ -> Shape (const (atom (c == '(')))
instance BackusNaurForm Shape where
  rule name (Shape x) = Shape $ \names ->
    if Set.member name names then atom False else x (Set.insert name names)
  ruleRec name f = rule name (f (Shape (const (atom False))))
instance CharGrammatical (Grammor Shape) where
  charPrecs shown readAt (Grammor (Shape x)) = Grammor $ Shape $
    fmap (map (\(FormShape _ _ grouped) -> FormShape shown readAt grouped)) . x
  charAt d g = Grammor (Shape (const (atom (shapedAt False d g))))
  charOperand d g = Grammor (Shape (const (atom (shapedAt True d g))))
  charGroup _ = Grammor (Shape (const (atom True)))
  charWord _ = Grammor (Shape (const (atom False)))
  charOperator _ = Grammor (Shape (const (atom False)))
  charLexeme = id
  charSpace = Grammor mempty
  charNamed names = Grammor $ Shape $ const $ Just
    [FormShape s r False | CharName {charShown = s, charRead = r} <- names]

-- | Whether a sub-term at a precedence may start with a parenthesis.
shapedAt
  :: forall a. Typeable a
  => Bool -> Prec -> (forall p. CharGrammatical p => p a a) -> Bool
shapedAt operand d g = parenthesized operand d forms
  || or [grouped | FormShape _ readAt grouped <- forms, d <= readAt]
  where
    forms = shapeOf @a g

-- Generating Bnfs --

{- | Defining rules once by name, so that rules which recur through
`Textual` instances are defined finitely.
-}
newtype Defining = Defining
  (ReaderT (Set String) (State (Map String RegString)) RegString)

definingG :: Grammor Defining a a -> RegBnf
definingG (Grammor (Defining defining)) =
  RegBnf (Bnf start (Set.fromList (Map.toList rules)))
  where
    (start, rules) = runState (runReaderT defining Set.empty) Map.empty

instance Semigroup Defining where
  Defining x <> Defining y = Defining (liftA2 (<>) x y)
instance Monoid Defining where
  mempty = Defining (pure mempty)
instance DisjunctiveMonoid Defining where
  falseP = Defining (pure falseP)
  Defining x >|< Defining y = Defining (liftA2 (>|<) x y)
instance KleeneStarAlgebra Defining where
  starK (Defining x) = Defining (starK <$> x)
  plusK (Defining x) = Defining (plusK <$> x)
  optK (Defining x) = Defining (optK <$> x)
instance Tokenized Char Defining where
  anyToken = Defining (pure anyToken)
  token = Defining . pure . token
  oneOf = Defining . pure . oneOf
  notOneOf = Defining . pure . notOneOf
  asIn = Defining . pure . asIn
  notAsIn = Defining . pure . notAsIn
instance TokenAlgebra Char Defining where
  tokenClass = Defining . pure . tokenClass
instance TerminalSymbol Char Defining where
  terminal = Defining . pure . terminal
instance BackusNaurForm Defining where
  rule name (Defining definition) = Defining $ do
    defining <- ask
    defined <- lift get
    unless (Set.member name defining || Map.member name defined) $ do
      defined' <- local (Set.insert name) definition
      lift (modify (Map.insert name defined'))
    pure (nonTerminal name)
  ruleRec name f = rule name (f (Defining (pure (nonTerminal name))))

-- Generics --

class GTextual f where
  gforms :: CharGrammatical p => [Either (CharName p (f x)) (p (f x) (f x))]
instance GTextual GHC.V1 where
  gforms = []
instance GTextual f => GTextual (GHC.D1 c f) where
  gforms = map (formVia m1) gforms
instance (GTextual f, GTextual g) => GTextual (f GHC.:+: g) where
  gforms = map (formVia l1) (gforms @f) <> map (formVia r1) (gforms @g)
    where
      l1 = prism' GHC.L1 (\case GHC.L1 a -> Just a; _ -> Nothing)
      r1 = prism' GHC.R1 (\case GHC.R1 a -> Just a; _ -> Nothing)
instance (GHC.Constructor c, GArgs f, GFields f, GInfix f)
  => GTextual (GHC.C1 c f) where
    gforms = map (formVia m1) forms
      where
        meta = GHC.M1 GHC.U1 :: GHC.C1 c GHC.U1 ()
        name = GHC.conName meta
        forms = case GHC.conFixity meta of
          GHC.Infix _ fixity -> [Right (ginfix @f fixity name)]
          GHC.Prefix
            | GHC.conIsRecord meta -> [named 10 11 (charSpace >* gfields @f)]
            | gnullary @f -> [named 11 11 (gargs @f)]
            | otherwise -> [named 10 10 (gargs @f)]
        named shown readAt g
          | isOperator name = Right $ charPrecs shown readAt $
              charGroup (charOperator name) >* g
          | otherwise = Left (CharName name shown readAt (const True) g)

-- | A form through a prism, or an isomorphism.
formVia
  :: Choice p
  => APrism' s a -> Either (CharName p a) (p a a)
  -> Either (CharName p s) (p s s)
formVia pat = withPrism pat $ \_ match -> \case
  Left n -> Left n
    { charShows = either (const False) (charShows n) . match
    , charForm = pat >? charForm n
    }
  Right g -> Right (pat >? g)

m1 :: Iso' (GHC.M1 i c f x) (f x)
m1 = iso GHC.unM1 GHC.M1

isOperator :: String -> Bool
isOperator = \case
  c : _ -> not (isAlpha c || c == '_')
  [] -> False

-- | The arguments of a prefix constructor.
class GArgs f where
  gargs :: CharGrammatical p => p (f x) (f x)
  gnullary :: Bool
  gnullary = False
instance GArgs GHC.U1 where
  gargs = dimap (const ()) (const GHC.U1) oneP
  gnullary = True
instance Textual a => GArgs (GHC.S1 s (GHC.K1 i a)) where
  gargs = iso (GHC.unK1 . GHC.unM1) (GHC.M1 . GHC.K1)
    >~ charSpace >* charTerm @a 11
instance (GArgs f, GArgs g) => GArgs (f GHC.:*: g) where
  gargs = iso (\(a GHC.:*: b) -> (a, b)) (uncurry (GHC.:*:))
    >~ gargs @f >*< gargs @g

-- | The fields of a record constructor.
class GFields f where
  gfields :: CharGrammatical p => p (f x) (f x)
instance GFields GHC.U1 where
  gfields = charPunct "{" >* dimap (const ()) (const GHC.U1) oneP
    *< charPunct "}"
instance (GHC.Selector s, Textual a) => GFields (GHC.S1 s (GHC.K1 i a)) where
  gfields = charPunct "{" >* gfield @s @a *< charPunct "}"
instance (GFieldList f, GFieldList g) => GFields (f GHC.:*: g) where
  gfields = charPunct "{" >* gfieldList @(f GHC.:*: g) *< charPunct "}"

-- | The fields of a record constructor, between its braces.
class GFieldList f where
  gfieldList :: CharGrammatical p => p (f x) (f x)
instance (GHC.Selector s, Textual a)
  => GFieldList (GHC.S1 s (GHC.K1 i a)) where
    gfieldList = gfield @s @a
instance (GFieldList f, GFieldList g) => GFieldList (f GHC.:*: g) where
  gfieldList = iso (\(a GHC.:*: b) -> (a, b)) (uncurry (GHC.:*:))
    >~ gfieldList @f *< charPunct "," *< charSpace >*< gfieldList @g

-- | A field of a record, @f = 1@.
gfield
  :: forall s a i x p. (GHC.Selector s, Textual a, CharGrammatical p)
  => p (GHC.S1 s (GHC.K1 i a) x) (GHC.S1 s (GHC.K1 i a) x)
gfield = iso (GHC.unK1 . GHC.unM1) (GHC.M1 . GHC.K1)
  >~ fieldName *< charSpace *< charOperator "=" *< charSpace
  >* charTerm @a 0
  where
    name = GHC.selName (GHC.M1 GHC.U1 :: GHC.S1 s GHC.U1 ())
    fieldName
      | isOperator name = charGroup (charOperator name)
      | otherwise = charWord name

-- | The operands of an infix constructor.
class GInfix f where
  ginfix :: CharGrammatical p => Prec -> String -> p (f x) (f x)
  ginfix _ _ = falseP
instance GInfix GHC.U1
instance GInfix (GHC.S1 s f)
instance (Textual a, Textual b)
  => GInfix (GHC.S1 s (GHC.K1 i a) GHC.:*: GHC.S1 t (GHC.K1 j b)) where
    ginfix fixity name = charPrec fixity $ pair
      >~ charOperandTerm @a (fixity + 1)
      *< charSpace *< infixed *< charSpace >*< charTerm @b (fixity + 1)
      where
        pair = iso
          (\(GHC.M1 (GHC.K1 a) GHC.:*: GHC.M1 (GHC.K1 b)) -> (a, b))
          (\(a, b) -> GHC.M1 (GHC.K1 a) GHC.:*: GHC.M1 (GHC.K1 b))
        infixed
          | isOperator name = charOperator name
          | otherwise = charPunct "`" >* charWord name *< charPunct "`"
instance {-# OVERLAPPABLE #-} GInfix (f GHC.:*: g)

-- Instances --

instance Textual Bool
instance Textual Ordering
instance Textual a => Textual (Maybe a)
instance (Textual a, Textual b) => Textual (Either a b)

instance Textual () where
  charGrammar = charGroup oneP

instance Textual a => Textual [a] where
  charGrammar = charListGrammar

-- | A tuple, by its items.
charTupled
  :: (GHC.Generic a, GTuple (GHC.Rep a), CharGrammatical p) => p a a
charTupled = charGroup (iso GHC.from GHC.to >~ gtuple)

-- | The items of a tuple.
class GTuple f where
  gtuple :: CharGrammatical p => p (f x) (f x)
instance GTuple f => GTuple (GHC.M1 i c f) where
  gtuple = m1 >~ gtuple
instance {-# OVERLAPPING #-} Textual a => GTuple (GHC.S1 s (GHC.K1 i a)) where
  gtuple = iso (GHC.unK1 . GHC.unM1) (GHC.M1 . GHC.K1)
    >~ charTerm @a 0
instance (GTuple f, GTuple g) => GTuple (f GHC.:*: g) where
  gtuple = iso (\(a GHC.:*: b) -> (a, b)) (uncurry (GHC.:*:))
    >~ gtuple @f *< charPunct "," >*< gtuple @g

instance (Textual a, Textual b) => Textual (a, b) where
  charGrammar = charTupled
instance (Textual a, Textual b, Textual c) => Textual (a, b, c) where
  charGrammar = charTupled
instance (Textual a, Textual b, Textual c, Textual d)
  => Textual (a, b, c, d) where
    charGrammar = charTupled
instance (Textual a, Textual b, Textual c, Textual d, Textual e)
  => Textual (a, b, c, d, e) where
    charGrammar = charTupled
instance (Textual a, Textual b, Textual c, Textual d, Textual e, Textual f)
  => Textual (a, b, c, d, e, f) where
    charGrammar = charTupled
instance
  ( Textual a, Textual b, Textual c, Textual d, Textual e, Textual f
  , Textual g
  ) => Textual (a, b, c, d, e, f, g) where
    charGrammar = charTupled
instance
  ( Textual a, Textual b, Textual c, Textual d, Textual e, Textual f
  , Textual g, Textual h
  ) => Textual (a, b, c, d, e, f, g, h) where
    charGrammar = charTupled
instance
  ( Textual a, Textual b, Textual c, Textual d, Textual e, Textual f
  , Textual g, Textual h, Textual i
  ) => Textual (a, b, c, d, e, f, g, h, i) where
    charGrammar = charTupled
instance
  ( Textual a, Textual b, Textual c, Textual d, Textual e, Textual f
  , Textual g, Textual h, Textual i, Textual j
  ) => Textual (a, b, c, d, e, f, g, h, i, j) where
    charGrammar = charTupled
instance
  ( Textual a, Textual b, Textual c, Textual d, Textual e, Textual f
  , Textual g, Textual h, Textual i, Textual j, Textual k
  ) => Textual (a, b, c, d, e, f, g, h, i, j, k) where
    charGrammar = charTupled
instance
  ( Textual a, Textual b, Textual c, Textual d, Textual e, Textual f
  , Textual g, Textual h, Textual i, Textual j, Textual k, Textual l
  ) => Textual (a, b, c, d, e, f, g, h, i, j, k, l) where
    charGrammar = charTupled
instance
  ( Textual a, Textual b, Textual c, Textual d, Textual e, Textual f
  , Textual g, Textual h, Textual i, Textual j, Textual k, Textual l
  , Textual m
  ) => Textual (a, b, c, d, e, f, g, h, i, j, k, l, m) where
    charGrammar = charTupled
instance
  ( Textual a, Textual b, Textual c, Textual d, Textual e, Textual f
  , Textual g, Textual h, Textual i, Textual j, Textual k, Textual l
  , Textual m, Textual n
  ) => Textual (a, b, c, d, e, f, g, h, i, j, k, l, m, n) where
    charGrammar = charTupled
instance
  ( Textual a, Textual b, Textual c, Textual d, Textual e, Textual f
  , Textual g, Textual h, Textual i, Textual j, Textual k, Textual l
  , Textual m, Textual n, Textual o
  ) => Textual (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o) where
    charGrammar = charTupled

-- | A constructor of one argument, @Identity 1@.
charApplied
  :: forall b a p. (Textual b, CharGrammatical p)
  => String -> Iso' a b -> p a a
charApplied name i = charNamed
  [CharName name 10 10 (const True) (i >~ charSpace >* charTerm @b 11)]

instance Textual a => Textual (Identity a) where
  charGrammar = charApplied "Identity" (iso runIdentity Identity)
instance (Textual a, Typeable b) => Textual (Const a b) where
  charGrammar = charApplied "Const" (iso getConst Const)
instance Textual a => Textual (Down a) where
  charGrammar = charApplied "Down" (iso getDown Down)
instance (Typeable f, Typeable g, Typeable a, Textual (f (g a)))
  => Textual (Compose f g a) where
    charGrammar = charApplied "Compose" (iso getCompose Compose)

-- | A collection, @fromList [a,b,c]@.
charFromList :: (Textual b, CharGrammatical p) => Iso' a [b] -> p a a
charFromList = charApplied "fromList"

instance (Ord k, Textual k, Textual v) => Textual (Map k v) where
  charGrammar = charFromList (iso Map.toList Map.fromList)
instance (Ord a, Textual a) => Textual (Set a) where
  charGrammar = charFromList (iso Set.toList Set.fromList)
instance Textual v => Textual (IntMap v) where
  charGrammar = charFromList (iso IntMap.toList IntMap.fromList)
instance Textual IntSet where
  charGrammar = charFromList (iso IntSet.toList IntSet.fromList)
instance Textual a => Textual (Seq a) where
  charGrammar = charFromList (iso toList Seq.fromList)
instance (Hashable k, Textual k, Textual v) => Textual (HashMap k v) where
  charGrammar = charFromList (iso HashMap.toList HashMap.fromList)
instance (Hashable a, Textual a) => Textual (HashSet a) where
  charGrammar = charFromList (iso HashSet.toList HashSet.fromList)

instance Textual Text.Text where
  charGrammar = iso Text.unpack Text.pack >~ charGrammar
instance Textual LText.Text where
  charGrammar = iso LText.unpack LText.pack >~ charGrammar
instance Textual ShortText.ShortText where
  charGrammar = iso ShortText.toString ShortText.fromString >~ charGrammar
instance Textual ByteString.ByteString where
  charGrammar = iso Char8.unpack Char8.pack >~ charGrammar
instance Textual LByteString.ByteString where
  charGrammar = iso LChar8.unpack LChar8.pack >~ charGrammar
instance Textual a => Textual (Vector.Vector a) where
  charGrammar = iso Vector.toList Vector.fromList >~ charGrammar

instance Textual Void where charGrammar = falseP

instance Textual a => Textual (NonEmpty a)
instance Textual a => Textual (Complex a)
instance Textual a => Textual (Solo a)
instance Typeable a => Textual (Proxy a)
instance Textual a => Textual (Tree a)
instance Textual a => Textual (ZipList a)
instance Textual Version
instance Textual GeneralCategory
instance Textual ExitCode
instance Textual IOMode where charGrammar = charEnumerated [ReadMode ..]
instance Textual SeekMode where charGrammar = charEnumerated [AbsoluteSeek ..]
instance Textual BufferMode where
  charGrammar = charNamed
    [ CharName "NoBuffering" 11 11 (\case NoBuffering -> True; _ -> False)
        (dimap (const ()) (const NoBuffering) oneP)
    , CharName "LineBuffering" 11 11 (\case LineBuffering -> True; _ -> False)
        (dimap (const ()) (const LineBuffering) oneP)
    , CharName "BlockBuffering" 10 10
        (\case BlockBuffering _ -> True; _ -> False)
        ( prism' BlockBuffering (\case BlockBuffering n -> Just n; _ -> Nothing)
          >? charSpace >* charTerm @(Maybe Int) 11 )
    ]
instance Textual a => Textual (Monoid.Sum a)
instance Textual a => Textual (Monoid.Product a)
instance Textual a => Textual (Monoid.Dual a)
instance Textual a => Textual (Monoid.First a)
instance Textual a => Textual (Monoid.Last a)
instance Textual Monoid.All
instance Textual Monoid.Any
instance (Typeable f, Typeable a, Textual (f a)) => Textual (Monoid.Alt f a)
instance (Typeable f, Typeable a, Textual (f a)) => Textual (Monoid.Ap f a)
instance Textual a => Textual (Semigroup.Min a)
instance Textual a => Textual (Semigroup.Max a)
instance Textual a => Textual (Semigroup.First a)
instance Textual a => Textual (Semigroup.Last a)
instance Textual a => Textual (Semigroup.WrappedMonoid a)
instance (Textual a, Textual b) => Textual (Semigroup.Arg a b)
instance (Typeable f, Typeable g, Typeable a, Textual (f a), Textual (g a))
  => Textual (Functor.Product f g a)
instance (Typeable f, Typeable g, Typeable a, Textual (f a), Textual (g a))
  => Textual (Functor.Sum f g a)

-- | An enumeration, of constructors named as `show` names them.
charEnumerated :: (Show a, Eq a, CharGrammatical p) => [a] -> p a a
charEnumerated as = charNamed
  [CharName (show a) 11 11 (== a) (dimap (const ()) (const a) oneP) | a <- as]

-- Numbers --

instance Textual Integer where charGrammar = charIntegral
instance Textual Int where charGrammar = charIntegral
instance Textual Int8 where charGrammar = charIntegral
instance Textual Int16 where charGrammar = charIntegral
instance Textual Int32 where charGrammar = charIntegral
instance Textual Int64 where charGrammar = charIntegral
instance Textual Word where charGrammar = charIntegral
instance Textual Word8 where charGrammar = charIntegral
instance Textual Word16 where charGrammar = charIntegral
instance Textual Word32 where charGrammar = charIntegral
instance Textual Word64 where charGrammar = charIntegral
instance Textual Natural where charGrammar = charIntegral
instance Textual CChar where charGrammar = charIntegral
instance Textual CSChar where charGrammar = charIntegral
instance Textual CUChar where charGrammar = charIntegral
instance Textual CShort where charGrammar = charIntegral
instance Textual CUShort where charGrammar = charIntegral
instance Textual CInt where charGrammar = charIntegral
instance Textual CUInt where charGrammar = charIntegral
instance Textual CLong where charGrammar = charIntegral
instance Textual CULong where charGrammar = charIntegral
instance Textual CLLong where charGrammar = charIntegral
instance Textual CULLong where charGrammar = charIntegral
instance Textual CPtrdiff where charGrammar = charIntegral
instance Textual CSize where charGrammar = charIntegral
instance Textual CWchar where charGrammar = charIntegral
instance Textual CSigAtomic where charGrammar = charIntegral
instance Textual CBool where charGrammar = charIntegral
instance Textual CIntPtr where charGrammar = charIntegral
instance Textual CUIntPtr where charGrammar = charIntegral
instance Textual CIntMax where charGrammar = charIntegral
instance Textual CUIntMax where charGrammar = charIntegral
instance Textual CFloat where charGrammar = charRealFloat
instance Textual CDouble where charGrammar = charRealFloat
instance Textual Double where charGrammar = charRealFloat
instance Textual Float where charGrammar = charRealFloat

{- | Integral numbers, by their literals, any of which parse,
printed as `show` does, parenthesized when negative above precedence 6.
Like @read@, a negative literal parses at any precedence.
-}
charIntegral :: (Integral a, CharGrammatical p) => p a a
charIntegral = orP
  [ nonNegative >? charLexeme integerG
  , charPrecs 6 11 $ negative >? charOperator "-" >* charLexeme integerG
  ]
  where
    nonNegative = prism' fromInteger $ \a ->
      let n = toInteger a in if n >= 0 then Just n else Nothing
    negative = prism' (fromInteger . negate) $ \a ->
      let n = toInteger a in if n < 0 then Just (negate n) else Nothing

{- | A non-negative integer literal, decimal, hexadecimal, octal or binary,
printed in decimal.
-}
integerG :: CharSyntactic p => p Integer Integer
integerG = iso (Decimal . show) numeralValue >~ numeralG

{- | Floating point numbers, by their literals, any of which parse,
@Infinity@ & @NaN@, & printed as `show` does,
parenthesized when negative above precedence 6.
-}
charRealFloat
  :: forall a p. (RealFloat a, Read a, Show a, CharGrammatical p) => p a a
charRealFloat = orP
  [ nonNegative >? charLexeme decimalLiteral
  , charNamed
    [ CharName "Infinity" 11 11 (\a -> isInfinite a && a > 0) (constant (1 / 0))
    , CharName "NaN" 11 11 isNaN (constant (0 / 0))
    ]
  , charPrecs 6 11 $ negative >? charOperator "-" >* orP
    [ charLexeme decimalLiteral
    , charNamed
      [ CharName "Infinity" 11 11 isInfinite (constant (1 / 0))
      , CharName "NaN" 11 11 isNaN (constant (0 / 0))
      ]
    ]
  ]
  where
    nonNegative = prism' id $ \a ->
      a <$ guard (not (isNaN a || isInfinite a || a < 0 || isNegativeZero a))
    negative = prism' negate $ \a ->
      negate a <$ guard (a < 0 || isNegativeZero a)
    constant :: a -> p a a
    constant a = dimap (const ()) (const a) oneP

{- | A non-negative decimal literal, of any of @read@'s forms,
printed as `show` does.
-}
decimalLiteral :: (Read a, Show a, CharSyntactic p) => p a a
decimalLiteral = iso (floatLiteral . show) floatValue >~ floatG

instance (HasResolution a, Typeable a) => Textual (Fixed a) where
  charGrammar = orP
    [ prism' id (\a -> a <$ guard (a >= 0)) >? charLexeme decimalLiteral
    , charPrecs 6 11 $ prism' negate (\a -> negate a <$ guard (a < 0))
      >? charOperator "-" >* charLexeme decimalLiteral
    ]

instance (Integral a, Textual a) => Textual (Ratio a) where
  charGrammar = charPrec 7 $
    iso (\r -> (numerator r, denominator r)) (uncurry (%))
    >~ charOperandTerm @a 8
    *< charSpace *< charOperator "%" *< charSpace >*< charTerm @a 8

-- | A floating point literal, decimal or an integer literal.
data FloatLiteral
  = FloatDecimal String (Maybe String) (Maybe (Maybe Char, String))
  | FloatInteger Numeral

floatValue :: Read a => FloatLiteral -> a
floatValue = \case
  FloatDecimal ds fraction expo -> read $ ds
    <> maybe "" ('.' :) fraction
    <> maybe "" (\(sign, es) -> 'e' : maybe "" pure sign <> es) expo
  FloatInteger numeral -> read (show (numeralValue numeral))

-- | How `show` prints a non-negative, finite floating point number.
floatLiteral :: String -> FloatLiteral
floatLiteral str = FloatDecimal ds fraction expo
  where
    (ds, rest) = span isDigit str
    (fraction, rest') = case rest of
      '.' : more -> let (fs, more') = span isDigit more in (Just fs, more')
      _ -> (Nothing, rest)
    expo = case rest' of
      'e' : '-' : es -> Just (Just '-', es)
      'e' : es -> Just (Nothing, es)
      _ -> Nothing

floatG :: CharSyntactic p => p FloatLiteral FloatLiteral
floatG = zero >|< decimal
  >? (oneOf ("123456789" :: String) >:< manyP digit) >*< fractionG >*< exponentG
  where
    zero = guarded startsWithZero ("0" >* afterZero)
    startsWithZero = \case
      FloatDecimal ('0' : _) _ _ -> True
      FloatDecimal _ _ _ -> False
      FloatInteger _ -> True
    afterZero = orP
      [ prism' FloatInteger
          (\case FloatInteger (Decimal _) -> Nothing
                 FloatInteger n -> Just n
                 _ -> Nothing)
          >? basedG
      , prism' (\(ds, (f, e)) -> FloatDecimal ('0' : ds) f e)
          (\case FloatDecimal ('0' : ds) f e -> Just (ds, (f, e)); _ -> Nothing)
          >? manyP digit >*< fractionG >*< exponentG
      ]
    decimal = prism' (\(ds, (f, e)) -> FloatDecimal ds f e)
      (\case FloatDecimal ds f e -> Just (ds, (f, e)); _ -> Nothing)
    fractionG = optionalP ("." >* someP digit)
    exponentG = optionalP $
      dimap (const 'e') (const ()) (oneOf ("eE" :: String))
      >* optionalP (oneOf ("+-" :: String)) >*< someP digit
    digit = oneOf ("0123456789" :: String)

-- | The forms of an integer literal.
data Numeral
  = Decimal String
  | Hexadecimal Char String
  | Octal Char String
  | Binary Char String

numeralValue :: Numeral -> Integer
numeralValue = \case
  Decimal ds -> digitsValue 10 ds
  Hexadecimal _ ds -> digitsValue 16 ds
  Octal _ ds -> digitsValue 8 ds
  Binary _ ds -> digitsValue 2 ds
  where
    digitsValue base = foldl' (\n c -> n * base + digitValue c) 0
    digitValue c
      | isDigit c = toInteger (ord c - ord '0')
      | c >= 'a' = toInteger (ord c - ord 'a' + 10)
      | otherwise = toInteger (ord c - ord 'A' + 10)

numeralG :: CharSyntactic p => p Numeral Numeral
numeralG = zero >|< decimal >? oneOf ("123456789" :: String) >:< manyP digit
  where
    zero = guarded startsWithZero ("0" >* afterZero)
    startsWithZero = \case
      Decimal ('0' : _) -> True
      Decimal _ -> False
      _ -> True
    afterZero = basedG >|< prism' (Decimal . ('0' :))
      (\case Decimal ('0' : ds) -> Just ds; _ -> Nothing)
      >? manyP digit
    decimal = prism' Decimal (\case Decimal ds -> Just ds; _ -> Nothing)
    digit = oneOf ("0123456789" :: String)

-- | A hexadecimal, octal or binary literal, after its @0@.
basedG :: CharSyntactic p => p Numeral Numeral
basedG = orP
  [ prism' (uncurry Hexadecimal)
      (\case Hexadecimal x ds -> Just (x, ds); _ -> Nothing)
      >? oneOf ("xX" :: String)
      >*< someP (oneOf ("0123456789abcdefABCDEF" :: String))
  , prism' (uncurry Octal) (\case Octal o ds -> Just (o, ds); _ -> Nothing)
      >? oneOf ("oO" :: String) >*< someP (oneOf ("01234567" :: String))
  , prism' (uncurry Binary) (\case Binary b ds -> Just (b, ds); _ -> Nothing)
      >? oneOf ("bB" :: String) >*< someP (oneOf ("01" :: String))
  ]

-- Characters & strings --

instance Textual Char where
  charGrammar = charLexeme ("'" >* charG *< "'")
  charListGrammar = charLexeme stringG >|< charBrackets

-- | A character literal's character, which may be escaped.
charG :: CharSyntactic p => p Char Char
charG = prism' litChar charOf ?< itemG
  where
    litChar c
      | c == '\'' = Escaped (EscChar '\'')
      | otherwise = case charItem c of
          Right e -> Escaped e
          Left c' -> Unescaped c'
    charOf = \case
      Unescaped c -> Just c
      Escaped e -> escapeValue e
    itemG = orP
      [ prism' Unescaped (\case Unescaped c -> Just c; _ -> Nothing)
          >? tokenClass (notOneOf ("'\\" :: String))
      , prism' Escaped (\case Escaped e -> Just e; _ -> Nothing)
          >? "\\" >* escapeG
      ]

-- | A character, unescaped or escaped.
data CharItem = Unescaped Char | Escaped Escape

-- | An escape sequence, after a backslash.
data Escape
  = EscChar Char -- ^ @\\n@, @\\\\@ & so on
  | EscCaret Char -- ^ @\\^A@
  | EscName String -- ^ @\\NUL@
  | EscDecimal String -- ^ @\\123@
  | EscOctal String -- ^ @\\o173@
  | EscHex String -- ^ @\\x7B@
  deriving stock (Eq, Show)

-- | How `show` prints a character, unescaped or escaped.
charItem :: Char -> Either Char Escape
charItem c
  | c > '\DEL' = Right (EscDecimal (show (ord c)))
  | c == '\DEL' = Right (EscName "DEL")
  | c == '\\' = Right (EscChar '\\')
  | c >= ' ' = Left c
  | Just e <- lookup c singleEscapes = Right (EscChar e)
  | otherwise = Right (EscName (asciiNames !! ord c))

singleEscapes :: [(Char, Char)]
singleEscapes =
  [ ('\a', 'a'), ('\b', 'b'), ('\f', 'f'), ('\n', 'n')
  , ('\r', 'r'), ('\t', 't'), ('\v', 'v') ]

asciiNames :: [String]
asciiNames =
  [ "NUL", "SOH", "STX", "ETX", "EOT", "ENQ", "ACK", "BEL"
  , "BS", "HT", "LF", "VT", "FF", "CR", "SO", "SI"
  , "DLE", "DC1", "DC2", "DC3", "DC4", "NAK", "SYN", "ETB"
  , "CAN", "EM", "SUB", "ESC", "FS", "GS", "RS", "US"
  , "SP", "DEL"
  ]

-- | The character of an escape, if it's in range.
escapeValue :: Escape -> Maybe Char
escapeValue = \case
  EscChar c ->
    Just (fromMaybe c (lookup c [(e, c') | (c', e) <- singleEscapes]))
  EscCaret c -> Just (chr (ord c - ord '@'))
  EscName name -> case lookup name (zip asciiNames ([0 .. 32] <> [127])) of
    Just n -> Just (chr n)
    Nothing -> Nothing
  EscDecimal ds -> code (read ds)
  EscOctal ds -> code (read ("0o" <> ds))
  EscHex ds -> code (read ("0x" <> ds))
  where
    code :: Integer -> Maybe Char
    code n
      | n <= 0x10FFFF = Just (chr (fromInteger n))
      | otherwise = Nothing

-- | An escape sequence, after a backslash, in a character literal.
escapeG :: CharSyntactic p => p Escape Escape
escapeG = orP
  [ prism' EscChar (\case EscChar c -> Just c; _ -> Nothing)
      >? oneOf ("abfnrtv\\\"'" :: String)
  , prism' EscCaret (\case EscCaret c -> Just c; _ -> Nothing)
      >? "^" >* oneOf ("@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_" :: String)
  , prism' EscDecimal (\case EscDecimal ds -> Just ds; _ -> Nothing)
      >? someP (oneOf ("0123456789" :: String))
  , prism' EscOctal (\case EscOctal ds -> Just ds; _ -> Nothing)
      >? "o" >* someP (oneOf ("01234567" :: String))
  , prism' EscHex (\case EscHex ds -> Just ds; _ -> Nothing)
      >? "x" >* someP (oneOf ("0123456789abcdefABCDEF" :: String))
  , trie
      [ (name, (== EscName name), dimap (const ()) (const (EscName name)) oneP)
      | name <- asciiNames ]
  ]

-- | An item of a string literal.
data StrItem
  = StrChar Char -- ^ an unescaped character
  | StrEscape Escape -- ^ an escape sequence
  | StrEmpty -- ^ @\\&@
  | StrGap -- ^ whitespace between backslashes
  deriving stock (Eq, Show)

-- | A string literal, @"abc"@.
stringG :: CharSyntactic p => p String String
stringG = prism' litString stringOf ?< "\"" >* stringBody
  where
    stringOf = fmap concat . traverse (\case
      StrChar c -> Just [c]
      StrEscape e -> pure <$> escapeValue e
      StrEmpty -> Just []
      StrGap -> Just [])

-- | How `show` prints a string's items, separating escapes by @\\&@.
litString :: String -> [StrItem]
litString = \case
  [] -> []
  c : rest -> case (charItem c, rest) of
    (Left '"', _) -> StrEscape (EscChar '"') : litString rest
    (Left c', _) -> StrChar c' : litString rest
    (Right e@(EscDecimal _), r : _) | isDigit r ->
      StrEscape e : StrEmpty : litString rest
    (Right e@(EscName "SO"), 'H' : _) ->
      StrEscape e : StrEmpty : litString rest
    (Right e, _) -> StrEscape e : litString rest

-- | What may not follow an escape sequence unescaped.
data Following = Anything | NotH | NotDigit | NotOctal | NotHex
  deriving stock (Eq, Show, Enum, Bounded)

{- | The rest of a string literal's items, & its closing quote.
After some escapes, some characters may not follow unescaped,
since @read@ would continue the escape with them,
so the rest is in one of several states, defined once & shared.
-}
stringBody :: CharSyntactic p => p [StrItem] [StrItem]
stringBody = anything
  where
    anything = rest Anything
    notH = rest NotH
    notDigit = rest NotDigit
    notOctal = rest NotOctal
    notHex = rest NotHex
    rest following = rule ("string-" <> show following) $ orP
      [ _Empty >? "\""
      , item (\case StrChar c | c `notElem` excluded -> Just c; _ -> Nothing)
          StrChar
          >? tokenClass (notOneOf excluded) >*< anything
      , guarded (\case StrChar _ : _ -> False; _ -> True) ("\\" >* escaped)
      ]
      where
        excluded :: String
        excluded = "\"\\" <> case following of
          Anything -> ""
          NotH -> "H"
          NotDigit -> "0123456789"
          NotOctal -> "01234567"
          NotHex -> "0123456789abcdefABCDEF"
    -- an escape sequence, after a backslash, & the rest of the string
    escaped = orP
      [ escape (\case EscChar c -> Just c; _ -> Nothing) EscChar
          >? oneOf ("abfnrtv\\\"'" :: String) >*< anything
      , escape (\case EscCaret c -> Just c; _ -> Nothing) EscCaret
          >? "^" >* oneOf ("@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_" :: String)
          >*< anything
      , escape (\case EscDecimal ds -> Just ds; _ -> Nothing) EscDecimal
          >? someP (oneOf ("0123456789" :: String)) >*< notDigit
      , escape (\case EscOctal ds -> Just ds; _ -> Nothing) EscOctal
          >? "o" >* someP (oneOf ("01234567" :: String)) >*< notOctal
      , escape (\case EscHex ds -> Just ds; _ -> Nothing) EscHex
          >? "x" >* someP (oneOf ("0123456789abcdefABCDEF" :: String))
          >*< notHex
      , item (\case StrEmpty -> Just (); _ -> Nothing) (const StrEmpty)
          >? "&" >* oneP >*< anything
      , parseOnly $ item (\case StrGap -> Just (); _ -> Nothing) (const StrGap)
          >? dimap (const " ") (const ()) (someP spaceG) >* "\\" >* oneP
          >*< anything
      , names
      ]
    names = trie
      [ ( name
        , \case StrEscape (EscName n) : _ -> n == name; _ -> False
        , prism' (StrEscape (EscName name) :)
            (\case StrEscape (EscName n) : items | n == name -> Just items
                   _ -> Nothing)
            >? if name == "SO" then notH else anything
        )
      | name <- asciiNames ]
    escape match build = item (\case StrEscape e -> match e; _ -> Nothing)
      (StrEscape . build)

-- | The first item of a list of items, & the rest.
item
  :: (StrItem -> Maybe x) -> (x -> StrItem)
  -> Prism' [StrItem] (x, [StrItem])
item match build = prism' (\(x, rest) -> build x : rest) $ \case
  i : rest | Just x <- match i -> Just (x, rest)
  _ -> Nothing
