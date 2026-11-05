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
which print as `show` does & parse what `read` does.

The one exception is redundant parentheses around a value which
starts with a parenthesis itself, a tuple or an infix constructor,
like @((1,2))@, which `read` accepts but no @LL(k)@ grammar can.
-}

module Control.Lens.Grammar.Char
  ( -- * Textual
    Textual (..)
  , charsShow
  , charsShowsPrec
  , charsRead
  , charsReadPrec
  , charsBnf
  , Textually (..)
    -- * Grammars
  , CharGrammar
  , CharGrammatical
  , Chars (..)
  , Alt (..)
  , Lead (..)
  , charsAt
  , charsWith
  , allLeads
  , leadsAt
  ) where

import Control.Lens hiding (Empty)
import Control.Lens.Grammar
import Control.Monad
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Reader (ReaderT, ask, local, runReaderT)
import Control.Monad.Trans.State.Strict
import Control.Applicative (ZipList (..))
import Data.ByteString qualified as ByteString
import Data.ByteString.Char8 qualified as Char8
import Data.ByteString.Lazy qualified as LByteString
import Data.ByteString.Lazy.Char8 qualified as LChar8
import Data.Char (chr, isAlpha, isDigit, ord)
import Data.Complex (Complex)
import Data.Fixed (Fixed, HasResolution)
import Data.Functor.Compose (Compose (..))
import Data.Functor.Product qualified as Functor
import Data.Functor.Sum qualified as Functor
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HashMap
import Data.HashSet (HashSet)
import Data.HashSet qualified as HashSet
import Data.Hashable (Hashable)
import Data.IntMap (IntMap)
import Data.IntMap qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.List.NonEmpty (NonEmpty)
import Data.Monoid qualified as Monoid
import Data.Ord (Down (..))
import Data.Proxy (Proxy)
import Data.Semigroup qualified as Semigroup
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.Text qualified as Text
import Data.Text.Lazy qualified as LText
import Data.Text.Short qualified as ShortText
import Data.Tree (Tree)
import Data.Tuple (Solo)
import Data.Vector qualified as Vector
import Data.Version (Version)
import Data.Void (Void)
import Foreign.C.Types
import System.Exit (ExitCode)
import System.IO (BufferMode (..), IOMode (..), SeekMode (..))
import Data.Function (on)
import Data.Int (Int8, Int16, Int32, Int64)
import Data.List (groupBy, sortOn)
import Data.Foldable (toList)
import Data.Kind (Constraint)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.Ratio (Ratio, denominator, numerator, (%))
import Data.Profunctor
import Data.Set (Set)
import Data.Set qualified as Set
import Data.String (IsString (..))
import Data.Word (Word8, Word16, Word32, Word64)
import GHC.Generics qualified as GHC
import Numeric.Natural (Natural)
import Text.ParserCombinators.ReadP qualified as ReadP
import Text.ParserCombinators.ReadPrec (ReadPrec, readP_to_Prec)
import Text.Read (Read (..))
import Type.Reflection (Typeable, typeRep)

-- Textual --

{- | A grammar of Haskell syntax, of characters.
-}
type CharGrammar a = forall p. CharGrammatical p => p a a

-- | The interpreters of a `CharGrammar`.
type CharGrammatical p =
  ( Lexical Char p
  , Alternator p
  , Cochoice p
  , forall x y. BackusNaurForm (p x y)
  , forall x y. (x ~ (), y ~ ()) => IsString (p x y)
  ) :: Constraint

{- | `Textual` types have grammars of Haskell's `Read` & `Show` syntax.

The forms of a type at a precedence, `charsPrec`, are like `showsPrec`
& `Text.Read.readPrec`: those which may appear unparenthesized
in a context of that precedence.
Redundant parentheses, & those required at a higher precedence,
are added by `charsAt`.
-}
class Typeable a => Textual a where
  charsPrec :: Int -> Chars a
  default charsPrec :: (GHC.Generic a, GTextual (GHC.Rep a)) => Int -> Chars a
  charsPrec d = charsVia (iso GHC.from GHC.to) (Chars (gchars d))
  {- | The forms of a list, like `showList` & `Text.Read.readListPrec`,
  by default in brackets, @[a,b,c]@. -}
  charsList :: Chars [a]
  charsList = charsBrackets

-- | `show`, by a `Textual` grammar.
charsShow :: Textual a => a -> String
charsShow a = charsShowsPrec 0 a ""

-- | `showsPrec`, by a `Textual` grammar.
charsShowsPrec :: forall a. Textual a => Int -> a -> ShowS
charsShowsPrec d a = fromMaybe (error "charsShowsPrec: unprintable") $
  printP (charsAt @a d allLeads) a

-- | `Text.Read.readMaybe`, by a `Textual` grammar, parsed predictively.
charsRead :: forall a. Textual a => String -> Maybe a
charsRead str =
  case parsecP (spaces "" >* charsAt @a 0 allLeads *< spaces "") str of
    ParsecState {parsecStream = "", parsecResult = Just a} -> Just a
    _ -> Nothing

-- | `Text.Read.readPrec`, by a `Textual` grammar, parsed predictively.
charsReadPrec :: forall a. Textual a => ReadPrec a
charsReadPrec = readP_to_Prec $ \d -> do
  str <- ReadP.look
  let parsed = parsecP (spaces "" >* charsAt @a d allLeads) str
  case parsecResult parsed of
    Nothing -> ReadP.pfail
    Just a -> a <$ replicateM_ (fromIntegral (parsecOffset parsed)) ReadP.get

-- | The `RegBnf` of a `Textual` type's grammar.
charsBnf :: forall a -> Textual a => RegBnf
charsBnf a = definingG (spaces "" >* charsAt @a 0 allLeads *< spaces "")

{- | `Show` & `Read` instances, derived from a `Textual` instance.

> data Point = Point {x :: Int, y :: Int}
>   deriving stock Generic
>   deriving anyclass Textual
>   deriving (Show, Read) via Textually Point
-}
newtype Textually a = Textually a

instance Textual a => Show (Textually a) where
  showsPrec d (Textually a) = charsShowsPrec d a
  showList as = charsShowsPrec 0 (map (\(Textually a) -> a) as)
instance Textual a => Read (Textually a) where
  readPrec = Textually <$> charsReadPrec
  readListPrec = map Textually <$> charsReadPrec

-- Grammars --

-- | A `CharGrammar`, as a value.
newtype CG a = CG (CharGrammar a)

{- | The first character of a form, by which spacing is decided,
since @read@'s lexer would merge a word with a following word,
or a symbol with a following symbol.
-}
data Lead
  = Word -- ^ a letter, digit or underscore
  | Symbol -- ^ an operator character, like @-@ or @:@
  | Paren -- ^ an opening parenthesis
  | Punct -- ^ any other punctuation, like @[@ or @"@
  deriving stock (Eq, Ord, Show, Read, Enum, Bounded)

-- | A form of a type's syntax.
data Alt a
  = Named String (a -> Bool) (CG a)
  {- ^ a constructor name, followed by a grammar, of values passing a test;
  named forms are factored by their names' characters,
  so that they're @LL(1)@ even when one name prefixes another -}
  | Plain (Set Lead) (Set Lead -> CG a)
  {- ^ a grammar, starting with characters of some `Lead`s,
  restricted to some of them -}
  | Parsed (Alt a)
  -- ^ a form which parses, but doesn't print

-- | A form starting with a character of a `Lead`.
plain :: Lead -> CharGrammar a -> Alt a
plain lead g = Plain (Set.singleton lead) (const (CG g))

-- | The forms of a type's syntax.
newtype Chars a = Chars [Alt a]
  deriving newtype (Semigroup, Monoid)

-- | Every `Lead`.
allLeads :: Set Lead
allLeads = Set.fromList [minBound .. maxBound]

-- | The `Lead`s of some forms.
leadsOf :: Chars a -> Set Lead
leadsOf (Chars alts) = Set.unions (map leadOf alts)
  where
    leadOf = \case
      Named {} -> Set.singleton Word
      Plain leads _ -> leads
      Parsed alt -> leadOf alt

{- | Whether some values of a `Textual` type are parenthesized
at a precedence, since fewer of its forms print there than at 0.
-}
parenthesizedAt :: forall a. Textual a => Int -> Bool
parenthesizedAt d = printed (charsPrec @a d) < printed (charsPrec @a 0)
  where
    printed (Chars alts) = length [() | alt <- alts, notParsed alt]
    notParsed = \case Parsed _ -> False; _ -> True

{- | The `Lead`s of a `Textual` type's operand at a precedence,
parenthesized only if some of its values must be, since a redundant
parenthesis would conflict with the parentheses of other operands.
-}
operandLeads :: forall a. Textual a => Int -> Set Lead
operandLeads d = leadsOf (charsPrec @a d)
  <> Set.fromList [Paren | parenthesizedAt @a d]

-- | The `Lead`s of a `Textual` type's grammar at a precedence.
leadsAt :: forall a. Textual a => Int -> Set Lead
leadsAt d = Set.insert Paren (leadsOf (charsPrec @a d))

-- | Forms through a prism, or an isomorphism.
charsVia :: APrism' s a -> Chars a -> Chars s
charsVia pat (Chars alts) = Chars (map (altVia pat) alts)

-- | A form through a prism, or an isomorphism.
altVia :: APrism' s a -> Alt a -> Alt s
altVia pat = \case
  Named name test (CG g) ->
    Named name (maybe False test . preview (clonePrism pat)) (CG (pat >? g))
  Plain leads k -> Plain leads (\ls -> case k ls of CG g -> CG (pat >? g))
  Parsed alt -> Parsed (altVia pat alt)

{- | A `Textual` type's grammar at a precedence, of its forms which start
with some `Lead`s, with parentheses around any of its forms,
unless one of its own forms starts with a parenthesis.
-}
charsAt :: forall a. Textual a => Int -> Set Lead -> CharGrammar a
charsAt d leads = rule name $ charsWith leads forms >|< wrapped
  where
    forms = charsPrec @a d
    wrapped
      | Paren `Set.notMember` leads || Paren `Set.member` leadsOf forms = falseP
      | otherwise =
          "(" >* spaces "" >* charsAt @a 0 allLeads *< spaces "" *< ")"
    name = show (typeRep @a)
      <> (if d == 0 then "" else "@" <> show d)
      <> concat ['-' : show lead | lead <- Set.toList (allLeads Set.\\ leads)]

-- | The forms which start with some `Lead`s, as a grammar.
charsWith :: Set Lead -> Chars a -> CharGrammar a
charsWith leads (Chars alts) = orP $
  [ trie [(name, test, g) | (name, test, CG g) <- named]
  | Word `Set.member` leads, not (null named) ]
  <> [ g
     | Plain ls k <- unparsed
     , let common = Set.intersection ls leads
     , not (Set.null common)
     , CG g <- [k common] ]
  where
    unparsed = map unparse alts
    named = [(name, test, g) | Named name test g <- unparsed]
    unparse = \case
      Parsed alt -> case unparse alt of
        Named name _ g -> Named name (const False) g
        Plain ls k -> Plain ls (\l -> case k l of CG g -> CG (parseOnly g))
        Parsed alt' -> alt'
      alt -> alt

{- | Factor named forms by their names' characters,
each branch printing the values of its names.
-}
trie :: CharGrammatical p => [(String, a -> Bool, p a a)] -> p a a
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
spaceG :: CharGrammar Char
spaceG = tokenClass (oneOf ("\t\n\v\f\r" :: String) >|< asIn Space)

-- | Optional whitespace, printed as given.
spaces :: String -> CharGrammar ()
spaces printed = dimap (const printed) (const ()) (manyP spaceG)

-- | Required whitespace, printed as given.
spaces1 :: String -> CharGrammar ()
spaces1 printed = dimap (const printed) (const ()) (someP spaceG)

{- | A grammar after a token of a `Lead`, separated by whitespace,
printed as given, which is required where @read@'s lexer would otherwise
merge the tokens.
-}
after :: Lead -> String -> (Set Lead -> CharGrammar a) -> CharGrammar a
after lead printed g = case lead of
  Word -> spaces1 printed >* g allLeads >|< g (Set.delete Word allLeads)
  Symbol -> spaces1 printed >* g allLeads >|< g (Set.delete Symbol allLeads)
  _ -> spaces printed >* g allLeads

-- | A list in brackets, @[a,b,c]@.
charsBrackets :: forall a. Textual a => Chars [a]
charsBrackets = Chars [plain Punct list]
  where
    list :: CharGrammar [a]
    list = "[" >* spaces "" >*
      ( _Empty >? "]"
      >|< _Cons >? listItem >*< manyP ("," >* spaces "" >* listItem) *< "]"
      )
    listItem :: CharGrammar a
    listItem = charsAt @a 0 allLeads *< spaces ""

-- Generating Bnfs --

{- | Defining rules once by name, so that rules which recur through
`Textual` instances, rather than `ruleRec`, are defined finitely.
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
  gchars :: Int -> [Alt (f x)]
instance GTextual GHC.V1 where
  gchars _ = []
instance GTextual f => GTextual (GHC.D1 c f) where
  gchars d = map (altVia m1) (gchars d)
instance (GTextual f, GTextual g) => GTextual (f GHC.:+: g) where
  gchars d = map (altVia l1) (gchars @f d) <> map (altVia r1) (gchars @g d)
    where
      l1 = prism' GHC.L1 (\case GHC.L1 a -> Just a; _ -> Nothing)
      r1 = prism' GHC.R1 (\case GHC.R1 a -> Just a; _ -> Nothing)
instance (GHC.Constructor c, GArgs f, GFields f, GInfix f)
  => GTextual (GHC.C1 c f) where
    gchars d = map (altVia m1) forms
      where
        name = GHC.conName (GHC.M1 GHC.U1 :: GHC.C1 c GHC.U1 ())
        operator = isOperator name
        forms = case GHC.conFixity (GHC.M1 GHC.U1 :: GHC.C1 c GHC.U1 ()) of
          GHC.Infix _ fixity
            | d <= fixity -> ginfix @f fixity name
            | otherwise -> []
          GHC.Prefix
            | GHC.conIsRecord (GHC.M1 GHC.U1 :: GHC.C1 c GHC.U1 ()) ->
                [ (if d <= 10 then id else Parsed) $ named $
                    spaces " " >* "{" >* spaces "" >* gfields @f
                    *< spaces "" *< "}"
                | d <= 11 ]
            | gnullary @f -> [named (gargs @f Word)]
            | d <= 10 -> [named (gargs @f Word)]
            | otherwise -> []
        named :: CharGrammar (f x) -> Alt (f x)
        named g
          | operator = plain Paren $ parenthesized name >* g
          | otherwise = Named name (const True) (CG g)

-- | An operator's name in parentheses, @(:+)@.
parenthesized :: String -> CharGrammar ()
parenthesized name = "(" >* spaces "" >* terminal name *< spaces "" *< ")"

m1 :: Iso' (GHC.M1 i c f x) (f x)
m1 = iso GHC.unM1 GHC.M1

isOperator :: String -> Bool
isOperator = \case
  c : _ -> not (isAlpha c || c == '_')
  [] -> False

-- | The arguments of a prefix constructor, after a token of a `Lead`.
class GArgs f where
  gargs :: Lead -> CharGrammar (f x)
  gnullary :: Bool
  gnullary = False
instance GArgs GHC.U1 where
  gargs _ = dimap (const ()) (const GHC.U1) oneP
  gnullary = True
instance Textual a => GArgs (GHC.S1 s (GHC.K1 i a)) where
  gargs lead = iso (GHC.unK1 . GHC.unM1) (GHC.M1 . GHC.K1)
    >~ after lead " " (charsAt @a 11)
instance (GArgs f, GArgs g) => GArgs (f GHC.:*: g) where
  gargs lead = iso (\(a GHC.:*: b) -> (a, b)) (uncurry (GHC.:*:))
    >~ gargs @f lead >*< gargs @g Word

-- | The fields of a record constructor.
class GFields f where
  gfields :: CharGrammar (f x)
instance GFields GHC.U1 where
  gfields = dimap (const ()) (const GHC.U1) oneP
instance (GHC.Selector s, Textual a) => GFields (GHC.S1 s (GHC.K1 i a)) where
  gfields = iso (GHC.unK1 . GHC.unM1) (GHC.M1 . GHC.K1)
    >~ field *< spaces " " *< "=" >* after Symbol " " (charsAt @a 0)
    where
      name = GHC.selName (GHC.M1 GHC.U1 :: GHC.S1 s GHC.U1 ())
      field :: CharGrammar ()
      field
        | isOperator name = parenthesized name
        | otherwise = terminal name
instance (GFields f, GFields g) => GFields (f GHC.:*: g) where
  gfields = iso (\(a GHC.:*: b) -> (a, b)) (uncurry (GHC.:*:))
    >~ gfields @f *< spaces "" *< "," *< spaces " " >*< gfields @g

-- | The operands of an infix constructor.
class GInfix f where
  ginfix :: Int -> String -> [Alt (f x)]
  ginfix _ _ = []
instance GInfix GHC.U1
instance GInfix (GHC.S1 s f)
instance (Textual a, Textual b)
  => GInfix (GHC.S1 s (GHC.K1 i a) GHC.:*: GHC.S1 t (GHC.K1 j b)) where
    ginfix fixity name =
      [ Plain (operandLeads @a (fixity + 1)) $ \leads -> CG $ pair
          >~ charsAt @a (fixity + 1) leads
          *< spaces " " *< opG >*< after opLead " " (charsAt @b (fixity + 1))
      ]
      where
        pair = iso
          (\(GHC.M1 (GHC.K1 a) GHC.:*: GHC.M1 (GHC.K1 b)) -> (a, b))
          (\(a, b) -> GHC.M1 (GHC.K1 a) GHC.:*: GHC.M1 (GHC.K1 b))
        opG :: CharGrammar ()
        opG
          | isOperator name = terminal name
          | otherwise = "`" >* spaces "" >* terminal name *< spaces "" *< "`"
        opLead
          | isOperator name = Symbol
          | otherwise = Punct
instance {-# OVERLAPPABLE #-} GInfix (f GHC.:*: g)

-- Instances --

instance Textual Bool
instance Textual Ordering
instance Textual a => Textual (Maybe a)
instance (Textual a, Textual b) => Textual (Either a b)

instance Textual () where
  charsPrec _ = Chars [plain Paren ("(" >* spaces "" >* ")")]

instance Textual a => Textual [a] where
  charsPrec _ = charsList

instance (Textual a, Textual b) => Textual (a, b) where
  charsPrec _ = charsTupled

instance (Textual a, Textual b, Textual c) => Textual (a, b, c) where
  charsPrec _ = charsTupled

instance
  ( Textual a, Textual b, Textual c, Textual d
  ) => Textual (a, b, c, d) where
    charsPrec _ = charsTupled

instance
  ( Textual a, Textual b, Textual c, Textual d, Textual e
  ) => Textual (a, b, c, d, e) where
    charsPrec _ = charsTupled

instance
  ( Textual a, Textual b, Textual c, Textual d, Textual e, Textual f
  ) => Textual (a, b, c, d, e, f) where
    charsPrec _ = charsTupled

instance
  ( Textual a, Textual b, Textual c, Textual d, Textual e, Textual f
  , Textual g
  ) => Textual (a, b, c, d, e, f, g) where
    charsPrec _ = charsTupled

instance
  ( Textual a, Textual b, Textual c, Textual d, Textual e, Textual f
  , Textual g, Textual h
  ) => Textual (a, b, c, d, e, f, g, h) where
    charsPrec _ = charsTupled

instance
  ( Textual a, Textual b, Textual c, Textual d, Textual e, Textual f
  , Textual g, Textual h, Textual i
  ) => Textual (a, b, c, d, e, f, g, h, i) where
    charsPrec _ = charsTupled

instance
  ( Textual a, Textual b, Textual c, Textual d, Textual e, Textual f
  , Textual g, Textual h, Textual i, Textual j
  ) => Textual (a, b, c, d, e, f, g, h, i, j) where
    charsPrec _ = charsTupled

instance
  ( Textual a, Textual b, Textual c, Textual d, Textual e, Textual f
  , Textual g, Textual h, Textual i, Textual j, Textual k
  ) => Textual (a, b, c, d, e, f, g, h, i, j, k) where
    charsPrec _ = charsTupled

instance
  ( Textual a, Textual b, Textual c, Textual d, Textual e, Textual f
  , Textual g, Textual h, Textual i, Textual j, Textual k, Textual l
  ) => Textual (a, b, c, d, e, f, g, h, i, j, k, l) where
    charsPrec _ = charsTupled

instance
  ( Textual a, Textual b, Textual c, Textual d, Textual e, Textual f
  , Textual g, Textual h, Textual i, Textual j, Textual k, Textual l
  , Textual m
  ) => Textual (a, b, c, d, e, f, g, h, i, j, k, l, m) where
    charsPrec _ = charsTupled

instance
  ( Textual a, Textual b, Textual c, Textual d, Textual e, Textual f
  , Textual g, Textual h, Textual i, Textual j, Textual k, Textual l
  , Textual m, Textual n
  ) => Textual (a, b, c, d, e, f, g, h, i, j, k, l, m, n) where
    charsPrec _ = charsTupled

instance
  ( Textual a, Textual b, Textual c, Textual d, Textual e, Textual f
  , Textual g, Textual h, Textual i, Textual j, Textual k, Textual l
  , Textual m, Textual n, Textual o
  ) => Textual (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o) where
    charsPrec _ = charsTupled

-- | A tuple, by its items.
charsTupled :: (GHC.Generic a, GTuple (GHC.Rep a)) => Chars a
charsTupled = charsTuple (iso GHC.from GHC.to >~ gtuple)

-- | The items of a tuple.
class GTuple f where
  gtuple :: CharGrammar (f x)
instance GTuple f => GTuple (GHC.M1 i c f) where
  gtuple = m1 >~ gtuple
instance {-# OVERLAPPING #-} Textual a => GTuple (GHC.S1 s (GHC.K1 i a)) where
  gtuple = iso (GHC.unK1 . GHC.unM1) (GHC.M1 . GHC.K1) >~ tupleItem @a
instance (GTuple f, GTuple g) => GTuple (f GHC.:*: g) where
  gtuple = iso (\(a GHC.:*: b) -> (a, b)) (uncurry (GHC.:*:))
    >~ gtuple @f *< "," *< spaces "" >*< gtuple @g

-- | A tuple of items.
charsTuple :: CharGrammar a -> Chars a
charsTuple items = Chars [plain Paren ("(" >* spaces "" >* items *< ")")]

-- | An item of a tuple.
tupleItem :: forall a. Textual a => CharGrammar a
tupleItem = charsAt @a 0 allLeads *< spaces ""

-- | A constructor of one argument, @Identity 1@, applied at precedence 10.
charsApplied :: forall b a. Textual b => String -> Iso' a b -> Int -> Chars a
charsApplied name i d =
  Chars
    [ Named name (const True) (CG (i >~ after Word " " (charsAt @b 11)))
    | d <= 10 ]

instance Textual a => Textual (Identity a) where
  charsPrec = charsApplied "Identity" (iso runIdentity Identity)
instance (Textual a, Typeable b) => Textual (Const a b) where
  charsPrec = charsApplied "Const" (iso getConst Const)
instance Textual a => Textual (Down a) where
  charsPrec = charsApplied "Down" (iso getDown Down)
instance (Typeable f, Typeable g, Typeable a, Textual (f (g a)))
  => Textual (Compose f g a) where
    charsPrec = charsApplied "Compose" (iso getCompose Compose)

-- | A collection, @fromList [a,b,c]@.
charsFromList :: Textual b => Iso' a [b] -> Int -> Chars a
charsFromList = charsApplied "fromList"

instance (Ord k, Textual k, Textual v) => Textual (Map k v) where
  charsPrec = charsFromList (iso Map.toList Map.fromList)
instance (Ord a, Textual a) => Textual (Set a) where
  charsPrec = charsFromList (iso Set.toList Set.fromList)
instance Textual v => Textual (IntMap v) where
  charsPrec = charsFromList (iso IntMap.toList IntMap.fromList)
instance Textual IntSet where
  charsPrec = charsFromList (iso IntSet.toList IntSet.fromList)
instance Textual a => Textual (Seq a) where
  charsPrec = charsFromList (iso toList Seq.fromList)
instance (Hashable k, Textual k, Textual v) => Textual (HashMap k v) where
  charsPrec = charsFromList (iso HashMap.toList HashMap.fromList)
instance (Hashable a, Textual a) => Textual (HashSet a) where
  charsPrec = charsFromList (iso HashSet.toList HashSet.fromList)

-- | A type by a list, or a string, which it shows as.
charsAs :: forall b a. Textual b => Iso' a b -> Int -> Chars a
charsAs i d = charsVia i (charsPrec @b d)

instance Textual Text.Text where charsPrec = charsAs (iso Text.unpack Text.pack)
instance Textual LText.Text where
  charsPrec = charsAs (iso LText.unpack LText.pack)
instance Textual ShortText.ShortText where
  charsPrec = charsAs (iso ShortText.toString ShortText.fromString)
instance Textual ByteString.ByteString where
  charsPrec = charsAs (iso Char8.unpack Char8.pack)
instance Textual LByteString.ByteString where
  charsPrec = charsAs (iso LChar8.unpack LChar8.pack)
instance Textual a => Textual (Vector.Vector a) where
  charsPrec = charsAs (iso Vector.toList Vector.fromList)

instance Textual Void where charsPrec _ = mempty

instance Textual a => Textual (NonEmpty a)
instance Textual a => Textual (Complex a)
instance Textual a => Textual (Solo a)
instance Typeable a => Textual (Proxy a)
instance Textual a => Textual (Tree a)
instance Textual a => Textual (ZipList a)
instance Textual Version
instance Textual GeneralCategory
instance Textual ExitCode
instance Textual IOMode where charsPrec _ = charsEnumerated [ReadMode ..]
instance Textual SeekMode where
  charsPrec _ = charsEnumerated [AbsoluteSeek ..]
instance Textual BufferMode where
  charsPrec d = Chars $
    [ Named "NoBuffering" (\case NoBuffering -> True; _ -> False)
        (CG (dimap (const ()) (const NoBuffering) oneP))
    , Named "LineBuffering" (\case LineBuffering -> True; _ -> False)
        (CG (dimap (const ()) (const LineBuffering) oneP))
    ] <> [ altVia
             (prism' BlockBuffering
               (\case BlockBuffering n -> Just n; _ -> Nothing))
             alt
         | Chars alts <- [charsApplied "BlockBuffering" (iso id id) d]
         , alt <- alts ]

-- | An enumeration, of constructors named as `show` names them.
charsEnumerated :: (Show a, Eq a) => [a] -> Chars a
charsEnumerated as = Chars
  [Named (show a) (== a) (CG (dimap (const ()) (const a) oneP)) | a <- as]
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

-- Numbers --

instance Textual Integer where charsPrec = charsIntegral
instance Textual Int where charsPrec = charsIntegral
instance Textual Int8 where charsPrec = charsIntegral
instance Textual Int16 where charsPrec = charsIntegral
instance Textual Int32 where charsPrec = charsIntegral
instance Textual Int64 where charsPrec = charsIntegral
instance Textual Word where charsPrec = charsIntegral
instance Textual Word8 where charsPrec = charsIntegral
instance Textual Word16 where charsPrec = charsIntegral
instance Textual Word32 where charsPrec = charsIntegral
instance Textual Word64 where charsPrec = charsIntegral
instance Textual Natural where charsPrec = charsIntegral
instance Textual CChar where charsPrec = charsIntegral
instance Textual CSChar where charsPrec = charsIntegral
instance Textual CUChar where charsPrec = charsIntegral
instance Textual CShort where charsPrec = charsIntegral
instance Textual CUShort where charsPrec = charsIntegral
instance Textual CInt where charsPrec = charsIntegral
instance Textual CUInt where charsPrec = charsIntegral
instance Textual CLong where charsPrec = charsIntegral
instance Textual CULong where charsPrec = charsIntegral
instance Textual CLLong where charsPrec = charsIntegral
instance Textual CULLong where charsPrec = charsIntegral
instance Textual CPtrdiff where charsPrec = charsIntegral
instance Textual CSize where charsPrec = charsIntegral
instance Textual CWchar where charsPrec = charsIntegral
instance Textual CSigAtomic where charsPrec = charsIntegral
instance Textual CBool where charsPrec = charsIntegral
instance Textual CIntPtr where charsPrec = charsIntegral
instance Textual CUIntPtr where charsPrec = charsIntegral
instance Textual CIntMax where charsPrec = charsIntegral
instance Textual CUIntMax where charsPrec = charsIntegral
instance Textual CFloat where charsPrec = charsRealFloat
instance Textual CDouble where charsPrec = charsRealFloat

{- | Integral numbers, by their literals, any of which parse,
& printed as `show` does, parenthesized when negative above precedence 6.
Like @read@, a negative literal parses at any precedence.
-}
charsIntegral :: Integral a => Int -> Chars a
charsIntegral d = Chars
  [ plain Word $ nonNegative >? integerG
  , (if d <= 6 then id else Parsed) $ plain Symbol $
      negative >? "-" >* spaces "" >* integerG
  ]
  where
    nonNegative = prism' fromInteger $ \a ->
      let n = toInteger a in if n >= 0 then Just n else Nothing
    negative = prism' (fromInteger . negate) $ \a ->
      let n = toInteger a in if n < 0 then Just (negate n) else Nothing

{- | A non-negative integer literal, decimal, hexadecimal, octal or binary,
printed in decimal.
-}
integerG :: CharGrammar Integer
integerG = iso (Decimal . show) numeralValue >~ numeralG

instance Textual Double where charsPrec = charsRealFloat
instance Textual Float where charsPrec = charsRealFloat

{- | Floating point numbers, by their literals, any of which parse,
@Infinity@ & @NaN@, & printed as `show` does,
parenthesized when negative above precedence 6.
-}
charsRealFloat :: forall a. (RealFloat a, Read a, Show a) => Int -> Chars a
charsRealFloat d = Chars
  [ plain Word $ nonNegative >? literal
  , Named "Infinity" (\a -> isInfinite a && a > 0) (CG (constant (1 / 0)))
  , Named "NaN" isNaN (CG (constant (0 / 0)))
  , (if d <= 6 then id else Parsed) $ plain Symbol $
      negative >? "-" >* spaces "" >* orP
        [ literal
        , charsWith (Set.singleton Word) $ Chars
          [ Named "Infinity" isInfinite (CG (constant (1 / 0)))
          , Named "NaN" isNaN (CG (constant (0 / 0)))
          ]
        ]
  ]
  where
    nonNegative = prism' id $ \a ->
      a <$ guard (not (isNaN a || isInfinite a || a < 0 || isNegativeZero a))
    negative = prism' negate $ \a ->
      negate a <$ guard (a < 0 || isNegativeZero a)
    literal :: CharGrammar a
    literal = decimalLiteral
    constant :: a -> CharGrammar a
    constant a = dimap (const ()) (const a) oneP

{- | A non-negative decimal literal, of any of @read@'s forms,
printed as `show` does.
-}
decimalLiteral :: (Read a, Show a) => CharGrammar a
decimalLiteral = iso (floatLiteral . show) floatValue >~ floatG

instance (HasResolution a, Typeable a) => Textual (Fixed a) where
  charsPrec d = Chars
    [ plain Word $ prism' id (\a -> a <$ guard (a >= 0)) >? decimalLiteral
    , (if d <= 6 then id else Parsed) $ plain Symbol $
        prism' negate (\a -> negate a <$ guard (a < 0))
        >? "-" >* spaces "" >* decimalLiteral
    ]

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

floatG :: CharGrammar FloatLiteral
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

instance (Integral a, Textual a) => Textual (Ratio a) where
  charsPrec d = Chars
    [ Plain (operandLeads @a 8) $ \leads -> CG $
        iso (\r -> (numerator r, denominator r)) (uncurry (%))
        >~ charsAt @a 8 leads
        *< spaces " " *< "%" >*< after Symbol " " (charsAt @a 8)
    | d <= 7 ]

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

numeralG :: CharGrammar Numeral
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
basedG :: CharGrammar Numeral
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
  charsPrec _ = Chars [plain Punct ("'" >* charG *< "'")]
  charsList = Chars [plain Punct stringG] <> charsBrackets

-- | A character literal's character, which may be escaped.
charG :: CharGrammar Char
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
escapeG :: CharGrammar Escape
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
      [ (name, (== EscName name), only' (EscName name))
      | name <- asciiNames ]
  ]
  where
    only' :: e -> CharGrammar e
    only' e = dimap (const ()) (const e) oneP

-- | An item of a string literal.
data StrItem
  = StrChar Char -- ^ an unescaped character
  | StrEscape Escape -- ^ an escape sequence
  | StrEmpty -- ^ @\\&@
  | StrGap -- ^ whitespace between backslashes
  deriving stock (Eq, Show)

-- | A string literal, @"abc"@.
stringG :: CharGrammar String
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
stringBody :: CharGrammar [StrItem]
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
          >? spaces1 " " >* "\\" >* oneP >*< anything
      , names
      ]
    names = trie
      [ ( name
        , \case StrEscape (EscName n) : _ -> n == name; _ -> False
        , prism' (StrEscape (EscName name) :)
            (\case StrEscape (EscName n) : rest | n == name -> Just rest
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
