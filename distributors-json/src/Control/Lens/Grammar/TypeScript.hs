{-# LANGUAGE OverloadedStrings #-}

{- |
Module      : Control.Lens.Grammar.TypeScript
Description : TypeScript declaration files, as a grammar
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable

TypeScript's declaration files, @.d.ts@, like the TypeScript compiler,
in two layers: `tsTokensGrammar` of their tokens, by their
`TsTokenCategory`s, & `tsGrammar` of their declarations, of those tokens,
by the compiler's names of their nodes, so that they parse & print
together.

Both layers parse by `parsecG` & print by `unparsecG`, locating failures,
since `tsTokensGrammar` scans tokens without their trivia, as the compiler
does. `tsGrammar` isn't @LL(1)@: it backtracks, by `try`, where TypeScript's
syntax needs more lookahead. Here, a declaration prints as tokens,
& as characters, & parses back.

>>> :set -XOverloadedStrings
>>> let point = ObjectType [PropertySignature [] (PropertyIdentifier "x") False (Just (KeywordType NumberKeyword))]
>>> let printed = unparsecG [TypeAliasDeclaration [ExportKeyword] "Point" [] point] ([] :: [TsToken])
>>> let source = parsecStream (unparsecG (parsecStream printed) ("" :: String))
>>> putStr source
export type Point = { x: number };
>>> parsecResult (parsecG @[TsDeclaration] (concat (parsecResult (parsecG @[TsToken] source)))) == Just [TypeAliasDeclaration [ExportKeyword] "Point" [] point]
True
-}

module Control.Lens.Grammar.TypeScript
  ( -- * Grammar
    tsGrammar
  , tsTokenGrammar
  , tsTokensGrammar
    -- * Declarations
  , TsDeclaration (..)
  , TsModuleName (..)
  , TsImportClause (..)
  , TsNamedBindings (..)
  , TsImportSpecifier (..)
  , TsModuleReference (..)
  , TsExportClause (..)
  , TsVariableDeclaration (..)
  , TsEnumMember (..)
  , TsHeritage (..)
  , TsEntityName
    -- * Types
  , TsType (..)
  , TsProperty (..)
  , TsPropertyName (..)
  , TsLiteral (..)
  , TsTypeParameter (..)
  , TsSignature (..)
  , TsParameter (..)
  , TsBindingName (..)
  , TsBindingElement (..)
    -- * Tokens
  , TsToken (..)
  , TsTokenCategory (..)
  ) where

import Control.Lens
import Control.Lens.Grammar
import Data.Char (chr, ord)
import Data.Maybe (fromMaybe)
import Data.Profunctor.Monadic.Do qualified as P
import Data.Text (Text)
import Data.Text qualified as Text

-- $setup
-- >>> import Control.Lens.Grammar

-- Declarations --

{- | A declaration of a declaration file, by the TypeScript compiler's
name of its node, most with its modifiers, like @export@ & @declare@.
-}
data TsDeclaration
  = TypeAliasDeclaration [TsTokenCategory] Text [TsTypeParameter] TsType
  -- ^ @type T\<U> = V;@
  | InterfaceDeclaration
      [TsTokenCategory] Text [TsTypeParameter] [TsHeritage] [TsProperty]
  -- ^ @interface I\<T> extends J { … }@
  | ClassDeclaration
      [TsTokenCategory] Text [TsTypeParameter]
      (Maybe TsHeritage) [TsHeritage] [TsProperty]
  -- ^ @class C\<T> extends D implements I { … }@
  | FunctionDeclaration [TsTokenCategory] Text TsSignature
  -- ^ @function f\<T>(x: T): U;@
  | VariableStatement
      [TsTokenCategory] TsTokenCategory [TsVariableDeclaration]
  -- ^ @const x: T;@, by @var@, @let@ or @const@
  | EnumDeclaration [TsTokenCategory] Text [TsEnumMember]
  -- ^ @enum E { A, B = 1 }@
  | ModuleDeclaration [TsTokenCategory] TsModuleName (Maybe [TsDeclaration])
  -- ^ @namespace N { … }@, @module "m" { … }@ or @global { … }@
  | ImportDeclaration Bool (Maybe TsImportClause) Text
  -- ^ @import type { A } from "m";@, of types only or not
  | ImportEqualsDeclaration [TsTokenCategory] Bool Text TsModuleReference
  -- ^ @import x = require("m");@, of types only or not
  | ExportDeclaration Bool TsExportClause (Maybe Text)
  -- ^ @export type { A } from "m";@, of types only or not
  | ExportAssignment Bool TsEntityName
  -- ^ @export = x;@, or else @export default x;@
  | NamespaceExportDeclaration Text
  -- ^ @export as namespace N;@
  deriving stock (Eq, Ord, Show, Read)

-- | The name of a `ModuleDeclaration`.
data TsModuleName
  = NamespaceName TsEntityName -- ^ @namespace N.M@
  | ModuleName TsEntityName -- ^ @module N.M@
  | ExternalModuleName Text -- ^ @module "m"@
  | GlobalAugmentation -- ^ @global@
  deriving stock (Eq, Ord, Show, Read)

-- | The imports of an `ImportDeclaration`, by default & by name.
data TsImportClause = TsImportClause (Maybe Text) (Maybe TsNamedBindings)
  deriving stock (Eq, Ord, Show, Read)

-- | Imports by name.
data TsNamedBindings
  = NamespaceImport Text -- ^ @* as n@
  | NamedImports [TsImportSpecifier] -- ^ @{ a, b as c }@
  deriving stock (Eq, Ord, Show, Read)

-- | @type a as b@, an import or export, of a type or not, renamed or not.
data TsImportSpecifier = TsImportSpecifier Bool (Maybe Text) Text
  deriving stock (Eq, Ord, Show, Read)

-- | What an `ImportEqualsDeclaration` imports.
data TsModuleReference
  = ExternalModuleReference Text -- ^ @require("m")@
  | EntityModuleReference TsEntityName -- ^ @N.M@
  deriving stock (Eq, Ord, Show, Read)

-- | What an `ExportDeclaration` exports.
data TsExportClause
  = NamespaceExport (Maybe Text) -- ^ @*@, or @* as n@
  | NamedExports [TsImportSpecifier] -- ^ @{ a, b as c }@
  deriving stock (Eq, Ord, Show, Read)

-- | @x: T = 1@, a variable, of a type or not, & a literal value or not.
data TsVariableDeclaration =
  TsVariableDeclaration Text (Maybe TsType) (Maybe TsLiteral)
  deriving stock (Eq, Ord, Show, Read)

-- | @A = 1@, a member of an `EnumDeclaration`, of a literal value or not.
data TsEnumMember = TsEnumMember TsPropertyName (Maybe TsLiteral)
  deriving stock (Eq, Ord, Show, Read)

-- | @N.M\<T>@, a class or interface which a declaration extends.
data TsHeritage = TsHeritage TsEntityName [TsType]
  deriving stock (Eq, Ord, Show, Read)

-- | A qualified name, @N.M.x@, by its identifiers.
type TsEntityName = [Text]

-- Types --

-- | A type, by the TypeScript compiler's name of its node.
data TsType
  = KeywordType TsTokenCategory -- ^ @number@, @string@, @never@, …
  | ThisType -- ^ @this@
  | LiteralType TsLiteral -- ^ @null@, @true@, @1@ or @"abc"@
  | ReferenceType TsEntityName [TsType] -- ^ @T@ or @N.T\<U, V>@
  | ArrayType TsType -- ^ @T[]@
  | TupleType [TsType] -- ^ @[T, U]@
  | OptionalType TsType -- ^ @T?@, an element of a tuple
  | RestType TsType -- ^ @...T@, an element of a tuple
  | NamedTupleMember Bool Text Bool TsType
  -- ^ @...x?: T@, an element of a tuple, rest or not, optional or not
  | UnionType [TsType] -- ^ @T | U@
  | IntersectionType [TsType] -- ^ @T & U@
  | ParenthesizedType TsType -- ^ @(T)@
  | FunctionType TsSignature -- ^ @\<T>(x: T) => U@
  | ConstructorType Bool TsSignature
  -- ^ @abstract new \<T>(x: T) => U@, abstract or not
  | TypeOperator TsTokenCategory TsType
  -- ^ @keyof T@, @readonly T@ or @unique T@
  | IndexedAccessType TsType TsType -- ^ @T[K]@
  | TypeQuery TsEntityName [TsType] -- ^ @typeof x\<T>@
  | ImportType Bool Text TsEntityName [TsType]
  -- ^ @typeof import("m").N.T\<U>@, a @typeof@ or not
  | InferType Text (Maybe TsType) -- ^ @infer T extends U@
  | TypePredicate Bool Text (Maybe TsType)
  -- ^ @asserts x is T@ or @this is T@, a return type, asserting or not
  | ObjectType [TsProperty] -- ^ @{ x: T; y?: U }@
  | MappedType
      (Maybe TsTokenCategory) Text TsType (Maybe TsType)
      (Maybe TsTokenCategory) TsType
  {- ^ @{ -readonly [K in T as U]+?: V }@, by its @readonly@ modifier,
  @readonly@, @+@ or @-@, its type parameter & its constraint & name type,
  & its @?@ modifier, @?@, @+@ or @-@ -}
  | ConditionalType TsType TsType TsType TsType
  -- ^ @T extends U ? V : W@
  | TemplateLiteralType Text [(TsType, Text)]
  -- ^ @\`a${T}b\`@, by its head & its spans' types & literals
  deriving stock (Eq, Ord, Show, Read)

{- | A member of an `ObjectType`, `InterfaceDeclaration` or
`ClassDeclaration`, by the TypeScript compiler's name of its node,
with its modifiers, like @readonly@ & @static@.
-}
data TsProperty
  = PropertySignature [TsTokenCategory] TsPropertyName Bool (Maybe TsType)
  -- ^ @x?: T@, optional or not, of a type or not
  | MethodSignature [TsTokenCategory] TsPropertyName Bool TsSignature
  -- ^ @f?\<T>(x: T): U@, optional or not
  | CallSignature TsSignature -- ^ @\<T>(x: T): U@
  | ConstructSignature TsSignature -- ^ @new \<T>(x: T): U@
  | IndexSignature [TsTokenCategory] Text TsType TsType -- ^ @[k: K]: T@
  | GetAccessor [TsTokenCategory] TsPropertyName (Maybe TsType)
  -- ^ @get x(): T@
  | SetAccessor [TsTokenCategory] TsPropertyName TsParameter
  -- ^ @set x(v: T)@
  | Constructor [TsTokenCategory] [TsParameter]
  -- ^ @constructor(x: T)@, of a class
  deriving stock (Eq, Ord, Show, Read)

-- | The name of a member.
data TsPropertyName
  = PropertyIdentifier Text -- ^ @x@
  | PropertyString Text -- ^ @"x y"@
  | PropertyNumeric Text -- ^ @1@
  | PropertyPrivate Text -- ^ @#x@
  | ComputedPropertyName TsEntityName -- ^ @[Symbol.iterator]@
  deriving stock (Eq, Ord, Show, Read)

-- | A literal, of a `LiteralType` or a value.
data TsLiteral
  = NullLiteral -- ^ @null@
  | TrueLiteral -- ^ @true@
  | FalseLiteral -- ^ @false@
  | TextLiteral Text -- ^ @"abc"@
  | NumberLiteral Text -- ^ @1@ or @-1.5@, as it's written
  | BigIntegerLiteral Text -- ^ @1n@ or @-1n@, as it's written
  deriving stock (Eq, Ord, Show, Read)

-- | @const T extends U = V@, a type parameter, with its modifiers.
data TsTypeParameter =
  TsTypeParameter [TsTokenCategory] Text (Maybe TsType) (Maybe TsType)
  deriving stock (Eq, Ord, Show, Read)

-- | @\<T>(x: T): U@, type parameters, parameters & a return type or not.
data TsSignature =
  TsSignature [TsTypeParameter] [TsParameter] (Maybe TsType)
  deriving stock (Eq, Ord, Show, Read)

-- | @...x?: T@, a parameter, rest or not, optional or not.
data TsParameter = TsParameter Bool TsBindingName Bool (Maybe TsType)
  deriving stock (Eq, Ord, Show, Read)

-- | The name of a parameter, or a pattern of names.
data TsBindingName
  = BindingIdentifier Text -- ^ @x@, or @this@
  | ObjectBindingPattern [TsBindingElement] -- ^ @{ a, b: c }@
  | ArrayBindingPattern [TsBindingElement] -- ^ @[a, ...b]@
  deriving stock (Eq, Ord, Show, Read)

-- | @...a: b@, an element of a binding pattern, rest or not.
data TsBindingElement =
  TsBindingElement Bool (Maybe TsPropertyName) TsBindingName
  deriving stock (Eq, Ord, Show, Read)

-- Tokens --

{- | A token, of a `TsTokenCategory` & its text, as the scanner of
the TypeScript compiler scans it, with its trivia: its text is
an identifier's name, a string's value, a number's spelling,
a template's literal, or a comment.
-}
data TsToken = TsToken
  { tokenCategory :: TsTokenCategory
  , tokenText :: Text
  } deriving stock (Eq, Ord, Show, Read)

instance Categorized TsToken where
  type Categorize TsToken = TsTokenCategory
  categorize = tokenCategory

-- | The categories of t'TsToken's, by the TypeScript compiler's names.
data TsTokenCategory
  = WhitespaceTrivia
  | NewLineTrivia
  | SingleLineCommentTrivia
  | MultiLineCommentTrivia
  | Identifier
  | PrivateIdentifier
  | StringLiteral
  | NumericLiteral
  | BigIntLiteral
  | NoSubstitutionTemplateLiteral
  | TemplateHead
  | TemplateMiddle
  | TemplateTail
  | OpenBraceToken
  | CloseBraceToken
  | OpenParenToken
  | CloseParenToken
  | OpenBracketToken
  | CloseBracketToken
  | DotToken
  | DotDotDotToken
  | SemicolonToken
  | CommaToken
  | LessThanToken
  | GreaterThanToken
  | QuestionToken
  | ColonToken
  | EqualsToken
  | EqualsGreaterThanToken
  | BarToken
  | AmpersandToken
  | MinusToken
  | PlusToken
  | AsteriskToken
  | ExclamationToken
  | ClassKeyword
  | ConstKeyword
  | DefaultKeyword
  | EnumKeyword
  | ExportKeyword
  | ExtendsKeyword
  | FalseKeyword
  | FunctionKeyword
  | ImportKeyword
  | InKeyword
  | NewKeyword
  | NullKeyword
  | ThisKeyword
  | TrueKeyword
  | TypeOfKeyword
  | VarKeyword
  | VoidKeyword
  | AbstractKeyword
  | AccessorKeyword
  | AnyKeyword
  | AsKeyword
  | AssertsKeyword
  | BigIntKeyword
  | BooleanKeyword
  | ConstructorKeyword
  | DeclareKeyword
  | FromKeyword
  | GetKeyword
  | GlobalKeyword
  | ImplementsKeyword
  | InferKeyword
  | InterfaceKeyword
  | IntrinsicKeyword
  | IsKeyword
  | KeyOfKeyword
  | LetKeyword
  | ModuleKeyword
  | NamespaceKeyword
  | NeverKeyword
  | NumberKeyword
  | ObjectKeyword
  | OutKeyword
  | OverrideKeyword
  | PrivateKeyword
  | ProtectedKeyword
  | PublicKeyword
  | ReadonlyKeyword
  | RequireKeyword
  | SetKeyword
  | StaticKeyword
  | StringKeyword
  | SymbolKeyword
  | TypeKeyword
  | UndefinedKeyword
  | UniqueKeyword
  | UnknownKeyword
  deriving stock (Eq, Ord, Show, Read, Enum, Bounded)

makeNestedPrisms ''TsDeclaration
makeNestedPrisms ''TsModuleName
makeNestedPrisms ''TsImportClause
makeNestedPrisms ''TsNamedBindings
makeNestedPrisms ''TsImportSpecifier
makeNestedPrisms ''TsModuleReference
makeNestedPrisms ''TsExportClause
makeNestedPrisms ''TsVariableDeclaration
makeNestedPrisms ''TsEnumMember
makeNestedPrisms ''TsHeritage
makeNestedPrisms ''TsType
makeNestedPrisms ''TsProperty
makeNestedPrisms ''TsPropertyName
makeNestedPrisms ''TsLiteral
makeNestedPrisms ''TsTypeParameter
makeNestedPrisms ''TsSignature
makeNestedPrisms ''TsParameter
makeNestedPrisms ''TsBindingName
makeNestedPrisms ''TsBindingElement

punctuation :: [(TsTokenCategory, Text)]
punctuation =
  [ (OpenBraceToken, "{"), (CloseBraceToken, "}")
  , (OpenParenToken, "("), (CloseParenToken, ")")
  , (OpenBracketToken, "["), (CloseBracketToken, "]")
  , (DotToken, "."), (DotDotDotToken, "..."), (SemicolonToken, ";")
  , (CommaToken, ","), (LessThanToken, "<"), (GreaterThanToken, ">")
  , (QuestionToken, "?"), (ColonToken, ":"), (EqualsToken, "=")
  , (EqualsGreaterThanToken, "=>"), (BarToken, "|"), (AmpersandToken, "&")
  , (MinusToken, "-"), (PlusToken, "+"), (AsteriskToken, "*")
  , (ExclamationToken, "!")
  ]

-- | Keywords which aren't identifiers.
reservedWords :: [(TsTokenCategory, Text)]
reservedWords =
  [ (ClassKeyword, "class"), (ConstKeyword, "const")
  , (DefaultKeyword, "default"), (EnumKeyword, "enum")
  , (ExportKeyword, "export"), (ExtendsKeyword, "extends")
  , (FalseKeyword, "false"), (FunctionKeyword, "function")
  , (ImportKeyword, "import"), (InKeyword, "in"), (NewKeyword, "new")
  , (NullKeyword, "null"), (ThisKeyword, "this"), (TrueKeyword, "true")
  , (TypeOfKeyword, "typeof"), (VarKeyword, "var"), (VoidKeyword, "void")
  ]

-- | Keywords which are also identifiers, by their context.
contextualKeywords :: [(TsTokenCategory, Text)]
contextualKeywords =
  [ (AbstractKeyword, "abstract"), (AccessorKeyword, "accessor")
  , (AnyKeyword, "any"), (AsKeyword, "as"), (AssertsKeyword, "asserts")
  , (BigIntKeyword, "bigint"), (BooleanKeyword, "boolean")
  , (ConstructorKeyword, "constructor"), (DeclareKeyword, "declare")
  , (FromKeyword, "from"), (GetKeyword, "get"), (GlobalKeyword, "global")
  , (ImplementsKeyword, "implements"), (InferKeyword, "infer")
  , (InterfaceKeyword, "interface"), (IntrinsicKeyword, "intrinsic")
  , (IsKeyword, "is"), (KeyOfKeyword, "keyof"), (LetKeyword, "let")
  , (ModuleKeyword, "module"), (NamespaceKeyword, "namespace")
  , (NeverKeyword, "never"), (NumberKeyword, "number")
  , (ObjectKeyword, "object"), (OutKeyword, "out")
  , (OverrideKeyword, "override"), (PrivateKeyword, "private")
  , (ProtectedKeyword, "protected"), (PublicKeyword, "public")
  , (ReadonlyKeyword, "readonly"), (RequireKeyword, "require")
  , (SetKeyword, "set"), (StaticKeyword, "static")
  , (StringKeyword, "string"), (SymbolKeyword, "symbol")
  , (TypeKeyword, "type"), (UndefinedKeyword, "undefined")
  , (UniqueKeyword, "unique"), (UnknownKeyword, "unknown")
  ]

keywords :: [(TsTokenCategory, Text)]
keywords = reservedWords <> contextualKeywords

-- | The token of a punctuation or keyword category.
symbol :: TsTokenCategory -> TsToken
symbol category =
  TsToken category (fromMaybe "" (lookup category (punctuation <> keywords)))

-- | One of some punctuation tokens, by its category.
symbolOf :: [TsTokenCategory] -> Prism' TsToken TsTokenCategory
symbolOf categories = prism' symbol $ \t ->
  if tokenCategory t `elem` categories && t == symbol (tokenCategory t)
    then Just (tokenCategory t) else Nothing

{- | A token, scanned from its characters. Its trivia, whitespace,
newlines & comments, are tokens, as the scanner of the TypeScript compiler
scans without skipping them. A @}@ is never a template's middle or tail,
which `tsTokensGrammar` rescans in its context, as the compiler's parser
rescans it.

A number is spelled by its digits, letters, separators & points,
as in @0xFF@, @1_000.5@ or @1n@, but not by a signed exponent.

It's a `RegGrammar`, since each token's spelling is a regular language.
-}
tsTokenGrammar :: RegGrammatical Char p => p TsToken TsToken
tsTokenGrammar = orP
  [ kindOf WhitespaceTrivia >? someP (oneOf @Char (" \t\f\v" :: String))
  , kindOf NewLineTrivia >? orP
      [only "\n" >? terminal "\n", only "\r\n" >? terminal "\r\n"]
  , _Comment >? terminal "/" >* orP
      [ _Left >? terminal "/" >* manyP (notOneOf @Char ("\r\n" :: String))
      , _Right >? blockComment
      ]
  , _Word >? identifierStart >:< manyP identifierPart
  , kindOf PrivateIdentifier >? terminal "#"
      >* (identifierStart >:< manyP identifierPart)
  , _Number >? asIn @Char DecimalNumber >:< manyP numberPart
  , kindOf StringLiteral >? orP
      [ terminal "\"" >* manyP (stringChar '"') *< terminal "\""
      , terminal "'" >* manyP (stringChar '\'') *< terminal "'"
      ]
  , _Template >? terminal "`" >* manyP templateChar >*< orP
      [ only NoSubstitutionTemplateLiteral >? terminal "`"
      , only TemplateHead >? terminal "${"
      ]
  , symbolOf [DotToken, DotDotDotToken] >? terminal "." >* orP
      [only DotDotDotToken >? terminal "..", only DotToken >? oneP]
  , symbolOf [EqualsToken, EqualsGreaterThanToken] >? terminal "=" >* orP
      [only EqualsGreaterThanToken >? terminal ">", only EqualsToken >? oneP]
  , orP
      [ only (TsToken category text) >? terminal (Text.unpack text)
      | (category, text) <- punctuation
      , category `notElem`
          [DotToken, DotDotDotToken, EqualsToken, EqualsGreaterThanToken]
      ]
  ]
  where
    identifierPart = orP
      [ identifierStart, asIn @Char DecimalNumber, asIn @Char NonSpacingMark
      , asIn @Char SpacingCombiningMark, asIn @Char ConnectorPunctuation
      ]
    numberPart = orP
      [ asIn @Char DecimalNumber, asIn @Char UppercaseLetter
      , asIn @Char LowercaseLetter, oneOf @Char ("_." :: String)
      ]
    -- @\*[^*]*\*+([^*/][^*]*\*+)*\/@, after its first @/@.
    blockComment = _BlockComment >? terminal "*"
      >* manyP (notOneOf @Char ("*" :: String))
      >*< someP (token '*')
      >*< manyP
        ( notOneOf @Char ("*/" :: String)
          >*< manyP (notOneOf @Char ("*" :: String))
          >*< someP (token '*')
        )
      *< terminal "/"

identifierStart :: RegGrammatical Char p => p Char Char
identifierStart = orP
  [ asIn @Char UppercaseLetter, asIn @Char LowercaseLetter
  , asIn @Char TitlecaseLetter, asIn @Char ModifierLetter
  , asIn @Char OtherLetter, asIn @Char LetterNumber
  , oneOf @Char ("_$" :: String)
  ]

stringChar :: RegGrammatical Char p => Char -> p Char Char
stringChar quote = orP
  [ notOneOf @Char (quote : '\\' : ['\0' .. '\31'])
  , terminal "\\" >* orP
      [ oneOf @Char ("\"\\/'" :: String)
      , only '\b' >? terminal "b", only '\f' >? terminal "f"
      , only '\n' >? terminal "n", only '\r' >? terminal "r"
      , only '\t' >? terminal "t"
      , terminal "u" >* (_HexCode >? replicateP 4 (digit (16 :: Int)))
      ]
  ]

templateChar :: RegGrammatical Char p => p Char Char
templateChar = orP
  [ notOneOf @Char ("`$\\" :: String)
  , terminal "\\" >* oneOf @Char ("`$\\" :: String)
  ]

{- | Tokens, scanned from their characters without their trivia,
as the TypeScript compiler's scanner skips trivia, & printed with them,
as `tsGrammar` prints them, so that `tsGrammar` parses by `parsecG`.
A @}@ which closes a template's substitution is scanned as the template's
middle or tail, by the depth of braces within the substitutions open,
as the compiler's parser rescans it.

It's a `CtxGrammar` by monadic bonding: each token is scanned in the
context of the tokens before it, whose braces & templates bond, by
@P.@`Data.Profunctor.Monadic.Do.>>=`, the depths that a @}@ is scanned by.
-}
tsTokensGrammar :: CtxGrammatical Char p => p [TsToken] [TsToken]
tsTokensGrammar = rmap
  (\scanned -> [t | t <- scanned, tokenCategory t `notElem` trivial])
  (tokensWithin [])
  where
    trivial =
      [ WhitespaceTrivia, NewLineTrivia
      , SingleLineCommentTrivia, MultiLineCommentTrivia
      ]

{- | Tokens, within the substitutions of templates, by the depth of braces
within each, innermost first.
-}
tokensWithin
  :: CtxGrammatical Char p
  => [Int] -> p [TsToken] [TsToken]
tokensWithin depths = orP
  [ _Cons >? (tokenWithin P.>>= tokensWithin . within depths)
  , _Empty >? oneP
  ]
  where
    tokenWithin = case depths of
      0 : _ -> orP [templateContinuation, tsTokenGrammar]
      _ -> tsTokenGrammar
    templateContinuation = _Template >? terminal "}"
      >* manyP templateChar >*< orP
        [ only TemplateTail >? terminal "`"
        , only TemplateMiddle >? terminal "${"
        ]
    within ds (TsToken category _) = case (category, ds) of
      (TemplateHead, _) -> 0 : ds
      (TemplateTail, _) -> drop 1 ds
      (OpenBraceToken, d : others) -> d + 1 : others
      (CloseBraceToken, d : others) -> d - 1 : others
      _ -> ds

-- | A token of a category, by its text.
kindOf :: TsTokenCategory -> Prism' TsToken String
kindOf category = prism'
  (TsToken category . Text.pack)
  (\(TsToken category' text) ->
    if category == category' then Just (Text.unpack text) else Nothing)

-- | An identifier or keyword, by its text.
_Word :: Prism' TsToken String
_Word = prism' word $ \(TsToken category text) ->
  if category == Identifier || category `elem` map fst keywords
    then Just (Text.unpack text) else Nothing
  where
    word chars = case lookup text [(t, k) | (k, t) <- keywords] of
      Just category -> TsToken category text
      Nothing -> TsToken Identifier text
      where
        text = Text.pack chars

-- | A number, or a big integer, which ends in @n@, by its spelling.
_Number :: Prism' TsToken String
_Number = prism' number $ \case
  TsToken NumericLiteral text -> Just (Text.unpack text)
  TsToken BigIntLiteral text -> Just (Text.unpack text)
  _ -> Nothing
  where
    number chars
      | not (null chars) && last chars == 'n' && '.' `notElem` chars =
          TsToken BigIntLiteral (Text.pack chars)
      | otherwise = TsToken NumericLiteral (Text.pack chars)

{- | A comment, by its text after its first @/@, of a line, after @//@,
or of a block, from its @*@.
-}
_Comment :: Prism' TsToken (Either String String)
_Comment = prism'
  (\case
    Left line -> TsToken SingleLineCommentTrivia (Text.pack ("//" <> line))
    Right block' -> TsToken MultiLineCommentTrivia (Text.pack ('/' : block')))
  (\case
    TsToken SingleLineCommentTrivia text ->
      Left . Text.unpack <$> Text.stripPrefix "//" text
    TsToken MultiLineCommentTrivia text ->
      Right . Text.unpack <$> Text.stripPrefix "/" text
    _ -> Nothing)

{- | A block comment's text, from its @*@, by the parts of
@\*[^*]*\*+([^*/][^*]*\*+)*\/@.
-}
_BlockComment
  :: Prism' String (String, (String, [(Char, (String, String))]))
_BlockComment = prism' build split
  where
    build (start, (stars, others)) = '*' : start <> stars
      <> concat [c : text <> more | (c, (text, more)) <- others] <> "/"
    split = \case
      '*' : str | not (null str), last str == '/' -> body (init str)
      _ -> Nothing
    body str =
      let
        (start, rest) = break (== '*') str
        (stars, others) = span (== '*') rest
      in
        if null stars then Nothing else (start,) . (stars,) <$> pieces others
    pieces = \case
      [] -> Just []
      c : str | c /= '*', c /= '/' ->
        let
          (text, rest) = break (== '*') str
          (more, others) = span (== '*') rest
        in
          if null more then Nothing
          else ((c, (text, more)) :) <$> pieces others
      _ -> Nothing

-- | A template's literal & its category.
_Template :: Prism' TsToken (String, TsTokenCategory)
_Template = prism'
  (\(chars, category) -> TsToken category (Text.pack chars))
  (\(TsToken category text) ->
    if category `elem` templates
      then Just (Text.unpack text, category) else Nothing)
  where
    templates =
      [NoSubstitutionTemplateLiteral, TemplateHead, TemplateMiddle, TemplateTail]

-- | A character, by the four hexadecimal digits of a @\\u@ escape.
_HexCode :: Prism' Char [Int]
_HexCode = prism'
  (chr . foldl' (\n d -> n * 16 + d) 0)
  (\c -> if ord c < 0x10000
    then Just [ord c `div` 16 ^ k `mod` 16 | k <- [3, 2, 1, 0 :: Int]] else Nothing)

-- Syntax --

-- | The interpreters of TypeScript's syntax.
type TsGrammatical p = CtxGrammatical TsToken p

{- | The declarations of a declaration file, of tokens, by the TypeScript
compiler's syntax, printed one per line, indented within blocks, & with
object types on one line. Trivia print conventionally, & parse only
from tokens with trivia, by `parseG`, since `tsTokensGrammar` scans
without them. Its @;@s print, & parse if they're there.

It's a `CtxGrammar` by `try`, rather than by monadic bonding, since it
isn't @LL(1)@: TypeScript's syntax needs more lookahead in places,
where it backtracks by `try`: declarations' & members' modifiers, imports'
forms & their @type@ & @as@, comma-separated lists after their first item,
members' signatures, constructors & accessors, a binding's name before
its @:@, type parameters' modifiers, @asserts@ & @is@ predicates,
function, conditional, @typeof import@, mapped & named tuple member types.

Printing a file, of many tokens, is linear into a stream which grows
at its end in constant time, like a `Data.Sequence.Seq`, rather than
a list.
-}
tsGrammar :: CtxGrammatical TsToken p => p [TsDeclaration] [TsDeclaration]
tsGrammar = manyP (declaration 0 *< newline)

-- | A declaration, at a depth of indentation.
declaration :: TsGrammatical p => Int -> p TsDeclaration TsDeclaration
declaration depth = rule "declaration" $ orP
  [ _Modified >? try
      ( orP
          [ only category >? tokenOf oneP category space
          | category <-
            [ ExportKeyword, DeclareKeyword, DefaultKeyword
            , AbstractKeyword, ConstKeyword
            ]
          ]
        >*< declaration depth
      )
  , _TypeAliasDeclaration . noModifiers >? tokenOf oneP TypeKeyword space
      >* identifier >*< typeParameters
      >*< tokenOf space EqualsToken space >* typeNode
      *< semicolon
  , _InterfaceDeclaration . noModifiers
      >? tokenOf oneP InterfaceKeyword space
      >* identifier >*< typeParameters
      >*< heritageClause ExtendsKeyword
      >*< block depth memberSeparator (const member)
  , _ClassDeclaration . noModifiers >? tokenOf oneP ClassKeyword space
      >* identifier >*< typeParameters
      >*< optionalP (tokenOf space ExtendsKeyword space >* heritage)
      >*< heritageClause ImplementsKeyword
      >*< block depth memberSeparator (const member)
  , _FunctionDeclaration . noModifiers
      >? tokenOf oneP FunctionKeyword space
      >* identifier >*< signature *< semicolon
  , _VariableStatement . noModifiers >? orP
      [ only category >? tokenOf oneP category space
      | category <- [VarKeyword, LetKeyword, ConstKeyword]
      ]
      >*< commas1 variable *< semicolon
  , _EnumDeclaration . noModifiers >? tokenOf oneP EnumKeyword space
      >* identifier >*< block depth enumSeparator (const enumMember)
  , _ModuleDeclaration . noModifiers >? orP
      [ _NamespaceName >? tokenOf oneP NamespaceKeyword space >* entityName
      , _ExternalModuleName >? try
          (tokenOf oneP ModuleKeyword space >* textOf StringLiteral)
      , _ModuleName >? tokenOf oneP ModuleKeyword space >* entityName
      , _GlobalAugmentation >? tokenOf oneP GlobalKeyword oneP
      ]
      >*< orP
        [ _Just >? block depth oneP declaration
        , only Nothing >? semicolon
        ]
  , _ImportEqualsDeclaration . noModifiers >? try
      ( tokenOf oneP ImportKeyword space >* typeOnly >*< identifier
        >*< tokenOf space EqualsToken space >* orP
          [ _ExternalModuleReference >? tokenOf oneP RequireKeyword oneP
              >* tokenOf oneP OpenParenToken oneP >* textOf StringLiteral
              *< tokenOf oneP CloseParenToken oneP
          , _EntityModuleReference >? entityName
          ]
        *< semicolon
      )
  , _BareImport >? try
      (tokenOf oneP ImportKeyword space >* textOf StringLiteral)
      *< semicolon
  , _ClauseImport >? tokenOf oneP ImportKeyword space >* typeOnly
      >*< importClause
      >*< tokenOf space FromKeyword space >* textOf StringLiteral
      *< semicolon
  , _Exported >? tokenOf oneP ExportKeyword oneP >* orP
      [ _ExportAssignment >? orP
          [ only True >? tokenOf space EqualsToken space
          , only False >? tokenOf space DefaultKeyword space
          ]
          >*< entityName *< semicolon
      , _NamespaceExportDeclaration >? tokenOf space AsKeyword space
          >* tokenOf oneP NamespaceKeyword space >* identifier *< semicolon
      , _ExportDeclaration >? space >* typeOnly
          >*< orP
            [ _NamespaceExport >? tokenOf oneP AsteriskToken oneP
                >* optionalP (tokenOf space AsKeyword space >* identifier)
            , _NamedExports >? braced specifier
            ]
          >*< optionalP
            (tokenOf space FromKeyword space >* textOf StringLiteral)
          *< semicolon
      ]
  ]
  where
    memberSeparator = printed (orP
      [tokenOf oneP SemicolonToken oneP, tokenOf oneP CommaToken oneP])
    enumSeparator = printed (tokenOf oneP CommaToken oneP)
    enumMember = _TsEnumMember >? propertyName
      >*< optionalP (tokenOf space EqualsToken space >* literal)

-- | Declarations without modifiers, which `_Modified` adds.
noModifiers :: Prism' ([TsTokenCategory], a) a
noModifiers = prism' ([],) $ \case
  ([], a) -> Just a
  _ -> Nothing

-- | A declaration, with a modifier.
_Modified :: Prism' TsDeclaration (TsTokenCategory, TsDeclaration)
_Modified = prism' (\(m, decl) -> over modifiers (m :) decl) $ \decl ->
  case decl ^? modifiers of
    Just (m : ms) -> Just (m, set modifiers ms decl)
    _ -> Nothing
  where
    modifiers :: Traversal' TsDeclaration [TsTokenCategory]
    modifiers f = \case
      TypeAliasDeclaration ms n t v ->
        (\ms' -> TypeAliasDeclaration ms' n t v) <$> f ms
      InterfaceDeclaration ms n t h b ->
        (\ms' -> InterfaceDeclaration ms' n t h b) <$> f ms
      ClassDeclaration ms n t e i b ->
        (\ms' -> ClassDeclaration ms' n t e i b) <$> f ms
      FunctionDeclaration ms n s ->
        (\ms' -> FunctionDeclaration ms' n s) <$> f ms
      VariableStatement ms k vs ->
        (\ms' -> VariableStatement ms' k vs) <$> f ms
      EnumDeclaration ms n es -> (\ms' -> EnumDeclaration ms' n es) <$> f ms
      ModuleDeclaration ms n b ->
        (\ms' -> ModuleDeclaration ms' n b) <$> f ms
      ImportEqualsDeclaration ms t n r ->
        (\ms' -> ImportEqualsDeclaration ms' t n r) <$> f ms
      decl -> pure decl

-- | An import of a module, for its effects.
_BareImport :: Prism' TsDeclaration Text
_BareImport = prism' (ImportDeclaration False Nothing) $ \case
  ImportDeclaration False Nothing name -> Just name
  _ -> Nothing

-- | An import, of types only or not, by its clause, from a module.
_ClauseImport :: Prism' TsDeclaration (Bool, (TsImportClause, Text))
_ClauseImport = prism'
  (\(types, (clause, name)) -> ImportDeclaration types (Just clause) name)
  (\case
    ImportDeclaration types (Just clause) name -> Just (types, (clause, name))
    _ -> Nothing)

-- | An export's declaration, which isn't a modified declaration.
_Exported :: Prism' TsDeclaration TsDeclaration
_Exported = prism' id $ \case
  decl@(ExportAssignment {}) -> Just decl
  decl@(NamespaceExportDeclaration _) -> Just decl
  decl@(ExportDeclaration {}) -> Just decl
  _ -> Nothing

-- | Whether an import or export is of types only.
typeOnly :: TsGrammatical p => p Bool Bool
typeOnly = orP
  [ only True >? try (tokenOf oneP TypeKeyword space)
  , only False >? oneP
  ]

importClause :: TsGrammatical p => p TsImportClause TsImportClause
importClause = _TsImportClause >? orP
  [ (_Just >? identifier) >*< orP
      [ _Just >? tokenOf oneP CommaToken space >* namedBindings
      , only Nothing >? oneP
      ]
  , (only Nothing >? oneP) >*< (_Just >? namedBindings)
  ]
  where
    namedBindings = orP
      [ _NamespaceImport >? tokenOf oneP AsteriskToken space
          >* tokenOf oneP AsKeyword space >* identifier
      , _NamedImports >? braced specifier
      ]

specifier :: TsGrammatical p => p TsImportSpecifier TsImportSpecifier
specifier = _TsImportSpecifier >? typeOnly
  >*< orP
    [ _Just >? try (identifierName *< tokenOf space AsKeyword space)
    , only Nothing >? oneP
    ]
  >*< identifierName

-- | A brace of comma separated items, on a line.
braced :: TsGrammatical p => p a a -> p [a] [a]
braced item = tokenOf oneP OpenBraceToken oneP >* orP
  [ _Empty >? tokenOf oneP CloseBraceToken oneP
  , space >* commas1 item
      *< tokenOf space CloseBraceToken oneP
  ]

variable :: TsGrammatical p => p TsVariableDeclaration TsVariableDeclaration
variable = _TsVariableDeclaration >? identifier
  >*< optionalP (tokenOf oneP ColonToken space >* typeNode)
  >*< optionalP (tokenOf space EqualsToken space >* literal)

-- | @extends@ or @implements@ & its heritage, or nothing for none.
heritageClause :: TsGrammatical p => TsTokenCategory -> p [TsHeritage] [TsHeritage]
heritageClause keyword = orP
  [ _Cons >? tokenOf space keyword space >* heritage
      >*< manyP (try (comma >* heritage))
  , _Empty >? oneP
  ]

heritage :: TsGrammatical p => p TsHeritage TsHeritage
heritage = _TsHeritage >? entityName >*< typeArguments

{- | A block of items, each on its line, indented & separated, or @{}@.
-}
block
  :: TsGrammatical p
  => Int -> p () () -> (Int -> p a a) -> p [a] [a]
block depth separator item = space >* tokenOf oneP OpenBraceToken oneP >* orP
  [ _Empty >? tokenOf oneP CloseBraceToken oneP
  , someP (indented (depth + 1) >* item (depth + 1) *< separator)
    *< indented depth *< tokenOf oneP CloseBraceToken oneP
  ]

-- | A member of an object type, interface or class.
member :: TsGrammatical p => p TsProperty TsProperty
member = ruleRec "member" $ \self -> orP
  [ _ModifiedMember >? try
      ( orP
          [ only category >? tokenOf oneP category space
          | category <-
            [ PublicKeyword, PrivateKeyword, ProtectedKeyword, StaticKeyword
            , ReadonlyKeyword, AbstractKeyword, OverrideKeyword
            , DeclareKeyword, AccessorKeyword
            ]
          ]
        >*< self
      )
  , _CallSignature >? signature
  , _ConstructSignature >? try (tokenOf oneP NewKeyword space >* signature)
  , _IndexSignature . noModifiers >? try
      ( tokenOf oneP OpenBracketToken oneP >* identifier
        *< tokenOf oneP ColonToken space
      )
      >*< typeNode *< tokenOf oneP CloseBracketToken oneP
      >*< tokenOf oneP ColonToken space >* typeNode
  , _Constructor . noModifiers >? try
      (tokenOf oneP ConstructorKeyword oneP >* parameters)
  , _GetAccessor . noModifiers >? try
      (tokenOf oneP GetKeyword space >* propertyName)
      >*< tokenOf oneP OpenParenToken oneP
      >* tokenOf oneP CloseParenToken oneP
      >* optionalP (tokenOf oneP ColonToken space >* typeNode)
  , _SetAccessor . noModifiers >? try
      (tokenOf oneP SetKeyword space >* propertyName)
      >*< tokenOf oneP OpenParenToken oneP >* parameter
      *< tokenOf oneP CloseParenToken oneP
  , _Named >? propertyName >*< question >*<
      ( signature
        >+< optionalP (tokenOf oneP ColonToken space >* typeNode)
      )
  ]

-- | A member, with a modifier.
_ModifiedMember :: Prism' TsProperty (TsTokenCategory, TsProperty)
_ModifiedMember = prism' (\(m, prop) -> over modifiers (m :) prop) $ \prop ->
  case prop ^? modifiers of
    Just (m : ms) -> Just (m, set modifiers ms prop)
    _ -> Nothing
  where
    modifiers :: Traversal' TsProperty [TsTokenCategory]
    modifiers f = \case
      PropertySignature ms n o t ->
        (\ms' -> PropertySignature ms' n o t) <$> f ms
      MethodSignature ms n o s ->
        (\ms' -> MethodSignature ms' n o s) <$> f ms
      IndexSignature ms n k t -> (\ms' -> IndexSignature ms' n k t) <$> f ms
      GetAccessor ms n t -> (\ms' -> GetAccessor ms' n t) <$> f ms
      SetAccessor ms n p -> (\ms' -> SetAccessor ms' n p) <$> f ms
      Constructor ms ps -> (\ms' -> Constructor ms' ps) <$> f ms
      prop -> pure prop

{- | A method or property without modifiers, by its name, whether it's
optional, & its signature or type.
-}
_Named
  :: Prism' TsProperty
      (TsPropertyName, (Bool, Either TsSignature (Maybe TsType)))
_Named = prism'
  (\case
    (name, (optional, Left sig)) -> MethodSignature [] name optional sig
    (name, (optional, Right t)) -> PropertySignature [] name optional t)
  (\case
    MethodSignature [] name optional sig -> Just (name, (optional, Left sig))
    PropertySignature [] name optional t -> Just (name, (optional, Right t))
    _ -> Nothing)

propertyName :: TsGrammatical p => p TsPropertyName TsPropertyName
propertyName = orP
  [ _PropertyIdentifier >? identifierName
  , _PropertyString >? textOf StringLiteral
  , _PropertyNumeric >? textOf NumericLiteral
  , _PropertyPrivate >? textOf PrivateIdentifier
  , _ComputedPropertyName >? tokenOf oneP OpenBracketToken oneP
      >* entityName *< tokenOf oneP CloseBracketToken oneP
  ]

-- | @\<T>(x: T): U@, with a return type or not.
signature :: TsGrammatical p => p TsSignature TsSignature
signature = _TsSignature >? typeParameters >*< parameters
  >*< optionalP (tokenOf oneP ColonToken space >* returnType)

parameters :: TsGrammatical p => p [TsParameter] [TsParameter]
parameters = tokenOf oneP OpenParenToken oneP
  >* commas parameter
  *< tokenOf oneP CloseParenToken oneP

parameter :: TsGrammatical p => p TsParameter TsParameter
parameter = _TsParameter >? dots >*< bindingName >*< question
  >*< optionalP (tokenOf oneP ColonToken space >* typeNode)

bindingName :: TsGrammatical p => p TsBindingName TsBindingName
bindingName = ruleRec "binding" $ \self -> orP
  [ _BindingIdentifier >? orP
      [identifier, only "this" >? tokenOf oneP ThisKeyword oneP]
  , _ObjectBindingPattern >? braced (bindingElement self)
  , _ArrayBindingPattern >? tokenOf oneP OpenBracketToken oneP
      >* commas (bindingElement self) *< tokenOf oneP CloseBracketToken oneP
  ]

-- | An element of a binding pattern, by a binding name.
bindingElement
  :: TsGrammatical p
  => p TsBindingName TsBindingName -> p TsBindingElement TsBindingElement
bindingElement name = _TsBindingElement >? dots
  >*< orP
    [ _Just >? try (propertyName *< tokenOf oneP ColonToken space)
    , only Nothing >? oneP
    ]
  >*< name

typeParameters :: TsGrammatical p => p [TsTypeParameter] [TsTypeParameter]
typeParameters = angled typeParameter

typeParameter :: TsGrammatical p => p TsTypeParameter TsTypeParameter
typeParameter = ruleRec "type parameter" $ \self -> orP
  [ _ModifiedParameter >? try
      ( orP
          [ only category >? tokenOf oneP category space
          | category <- [ConstKeyword, InKeyword, OutKeyword]
          ]
        >*< self
      )
  , _TsTypeParameter . noModifiers >? identifier
      >*< optionalP (tokenOf space ExtendsKeyword space >* typeNode)
      >*< optionalP (tokenOf space EqualsToken space >* typeNode)
  ]

-- | A type parameter, with a modifier.
_ModifiedParameter
  :: Prism' TsTypeParameter (TsTokenCategory, TsTypeParameter)
_ModifiedParameter = prism'
  (\(m, TsTypeParameter ms n c d) -> TsTypeParameter (m : ms) n c d)
  (\case
    TsTypeParameter (m : ms) n c d -> Just (m, TsTypeParameter ms n c d)
    _ -> Nothing)

-- | Type arguments, @\<T, U>@, or none.
typeArguments :: TsGrammatical p => p [TsType] [TsType]
typeArguments = angled typeNode

-- | @\<a, b>@, or nothing for none.
angled :: TsGrammatical p => p a a -> p [a] [a]
angled item = orP
  [ _Cons >? tokenOf oneP LessThanToken oneP >* item
      >*< manyP (try (comma >* item))
      *< optionalToken CommaToken
      *< tokenOf oneP GreaterThanToken oneP
  , _Empty >? oneP
  ]

-- | A return type, which may be a type predicate.
returnType :: TsGrammatical p => p TsType TsType
returnType = orP
  [ _AssertsPredicate >? try (tokenOf oneP AssertsKeyword space >* name)
      >*< optionalP (tokenOf space IsKeyword space >* typeNode)
  , _IsPredicate >? try (name *< tokenOf space IsKeyword space)
      >*< typeNode
  , typeNode
  ]
  where
    name = orP [identifier, only "this" >? tokenOf oneP ThisKeyword oneP]

-- | An asserting type predicate.
_AssertsPredicate :: Prism' TsType (Text, Maybe TsType)
_AssertsPredicate = prism' (uncurry (TypePredicate True)) $ \case
  TypePredicate True name t -> Just (name, t)
  _ -> Nothing

-- | A type predicate, which isn't asserting.
_IsPredicate :: Prism' TsType (Text, TsType)
_IsPredicate = prism'
  (\(name, t) -> TypePredicate False name (Just t))
  (\case
    TypePredicate False name (Just t) -> Just (name, t)
    _ -> Nothing)

-- | A type.
typeNode :: TsGrammatical p => p TsType TsType
typeNode = ruleRec "type" $ \ty -> orP
  [ _FunctionType . _Arrow >? try functionSignature
  , _ConstructorType . aside _Arrow >? constructorSignature
  , _Conditional >~ unionType ty >*< optionalP
      ( tokenOf space ExtendsKeyword space >* orP
          [ _FunctionType . _Arrow >? try functionSignature
          , _ConstructorType . aside _Arrow >? constructorSignature
          , unionType ty
          ]
        >*< tokenOf space QuestionToken space >* ty
        >*< tokenOf space ColonToken space >* ty
      )
  ]
  where
    functionSignature = typeParameters >*< parameters
      >*< tokenOf space EqualsGreaterThanToken space >* returnType
    constructorSignature = orP
      [ only True >? tokenOf oneP AbstractKeyword space
      , only False >? oneP
      ]
      >*< tokenOf oneP NewKeyword space >* functionSignature

-- | A signature, with a return type.
_Arrow :: Prism' TsSignature ([TsTypeParameter], ([TsParameter], TsType))
_Arrow = prism'
  (\(tps, (ps, r)) -> TsSignature tps ps (Just r))
  (\case
    TsSignature tps ps (Just r) -> Just (tps, (ps, r))
    _ -> Nothing)

unionType :: TsGrammatical p => p TsType TsType -> p TsType TsType
unionType ty = rule "union" $ _Several _UnionType
  >~ leading BarToken >* intersectionType ty >*< manyP
    (tokenOf space BarToken space >* intersectionType ty)

intersectionType :: TsGrammatical p => p TsType TsType -> p TsType TsType
intersectionType ty = rule "intersection" $ _Several _IntersectionType
  >~ leading AmpersandToken >* operatorType ty >*< manyP
    (tokenOf space AmpersandToken space >* operatorType ty)

-- | A leading operator, which is parsed but not printed.
leading :: TsGrammatical p => TsTokenCategory -> p () ()
leading category = dimap (const Nothing) (const ())
  (optionalP (tokenOf oneP category space))

operatorType :: TsGrammatical p => p TsType TsType -> p TsType TsType
operatorType ty = ruleRec "operator" $ \self -> orP
  [ _TypeOperator >? orP
      [ only category >? tokenOf oneP category space
      | category <- [KeyOfKeyword, UniqueKeyword, ReadonlyKeyword]
      ]
      >*< self
  , _InferType >? tokenOf oneP InferKeyword space >* identifier
      >*< optionalP
        (try (tokenOf space ExtendsKeyword space >* unionType ty))
  , postfixType ty
  ]

postfixType :: TsGrammatical p => p TsType TsType -> p TsType TsType
postfixType ty = rule "postfix" $ _Postfix
  >~ primaryType ty >*< manyP
    ( tokenOf oneP OpenBracketToken oneP >* orP
        [ only Nothing >? tokenOf oneP CloseBracketToken oneP
        , _Just >? ty *< tokenOf oneP CloseBracketToken oneP
        ]
    )

-- | A type of any arrays & indexed accesses of a type.
_Postfix :: Iso' TsType (TsType, [Maybe TsType])
_Postfix = iso postfixes (uncurry (foldl postfix))
  where
    postfixes = \case
      ArrayType node -> (<> [Nothing]) <$> postfixes node
      IndexedAccessType node key -> (<> [Just key]) <$> postfixes node
      node -> (node, [])
    postfix node = \case
      Nothing -> ArrayType node
      Just key -> IndexedAccessType node key

primaryType :: TsGrammatical p => p TsType TsType -> p TsType TsType
primaryType ty = rule "primary" $ orP
  [ _KeywordType >? orP
      [ only category >? tokenOf oneP category oneP
      | category <-
        [ AnyKeyword, BigIntKeyword, BooleanKeyword, IntrinsicKeyword
        , NeverKeyword, NumberKeyword, ObjectKeyword, StringKeyword
        , SymbolKeyword, UndefinedKeyword, UnknownKeyword, VoidKeyword
        ]
      ]
  , only ThisType >? tokenOf oneP ThisKeyword oneP
  , _LiteralType >? literal
  , _NoSubstitution >? textOf NoSubstitutionTemplateLiteral
  , _TemplateLiteralType >? textOf TemplateHead >*< templateSpans
  , _TypeOfImport >? try
      (tokenOf oneP TypeOfKeyword space >* importType)
  , _TypeImport >? importType
  , _TypeQuery >? tokenOf oneP TypeOfKeyword space >* entityName
      >*< typeArguments
  , _ReferenceType >? entityName >*< typeArguments
  , _TupleType >? tokenOf oneP OpenBracketToken oneP >* orP
      [ _Empty >? tokenOf oneP CloseBracketToken oneP
      , commas1 tupleElement
          *< tokenOf oneP CloseBracketToken oneP
      ]
  , _ParenthesizedType >? tokenOf oneP OpenParenToken oneP
      >* ty *< tokenOf oneP CloseParenToken oneP
  , _Braced >? tokenOf oneP OpenBraceToken oneP >* orP
      [ only (ObjectType []) >? tokenOf oneP CloseBraceToken oneP
      , _MappedType >? try mappedType
      , _ObjectType >? space >* (_Cons >? member >*< moreMembers)
      ]
  ]
  where
    importType = tokenOf oneP ImportKeyword oneP
      >* tokenOf oneP OpenParenToken oneP >* textOf StringLiteral
      *< tokenOf oneP CloseParenToken oneP
      >*< manyP (tokenOf oneP DotToken oneP >* identifierName)
      >*< typeArguments
    templateSpans = ruleRec "spans" $ \rest -> _Spans >? ty
      >*< (textOf TemplateMiddle >*< rest >+< textOf TemplateTail)
    tupleElement = rule "element" $ orP
      [ _NamedTupleMember . iso (\(r, (n, (o, t))) -> ((r, (n, o)), t)) (\((r, (n, o)), t) -> (r, (n, (o, t)))) >? try
          (dots >*< identifier >*< question *< tokenOf oneP ColonToken space)
          >*< ty
      , _RestType >? tokenOf oneP DotDotDotToken oneP >* ty
      , _Optional >~ ty >*< question
      ]
    mappedType = space >* orP
      [ only (Just PlusToken) >? tokenOf oneP PlusToken oneP
          >* tokenOf oneP ReadonlyKeyword space
      , only (Just MinusToken) >? tokenOf oneP MinusToken oneP
          >* tokenOf oneP ReadonlyKeyword space
      , only (Just ReadonlyKeyword) >? tokenOf oneP ReadonlyKeyword space
      , only Nothing >? oneP
      ]
      >*< tokenOf oneP OpenBracketToken oneP >* identifier
      >*< tokenOf space InKeyword space >* ty
      >*< optionalP (tokenOf space AsKeyword space >* ty)
      >*< tokenOf oneP CloseBracketToken oneP >* orP
        [ only (Just PlusToken) >? tokenOf oneP PlusToken oneP
            >* tokenOf oneP QuestionToken oneP
        , only (Just MinusToken) >? tokenOf oneP MinusToken oneP
            >* tokenOf oneP QuestionToken oneP
        , only (Just QuestionToken) >? tokenOf oneP QuestionToken oneP
        , only Nothing >? oneP
        ]
      >*< tokenOf oneP ColonToken space >* ty
      *< optionalToken SemicolonToken
      *< tokenOf space CloseBraceToken oneP
    -- The members after an object type's first, on its line, separated
    -- by @;@ or @,@, or by nothing, & its closing brace.
    moreMembers = ruleRec "members" $ \rest -> orP
      [ _Empty >? tokenOf space CloseBraceToken oneP
      , orP
          [ tokenOf oneP SemicolonToken oneP
          , tokenOf oneP CommaToken oneP
          ]
        >* orP
          [ _Empty >? tokenOf space CloseBraceToken oneP
          , _Cons >? space >* member >*< rest
          ]
      , _Cons >? space >* member >*< rest
      ]

-- | An import type, without its @typeof@.
_TypeImport :: Prism' TsType (Text, (TsEntityName, [TsType]))
_TypeImport = prism'
  (\(name, (qualifier, args)) -> ImportType False name qualifier args)
  (\case
    ImportType False name qualifier args -> Just (name, (qualifier, args))
    _ -> Nothing)

-- | An import type, with its @typeof@.
_TypeOfImport :: Prism' TsType (Text, (TsEntityName, [TsType]))
_TypeOfImport = prism'
  (\(name, (qualifier, args)) -> ImportType True name qualifier args)
  (\case
    ImportType True name qualifier args -> Just (name, (qualifier, args))
    _ -> Nothing)

-- | A literal.
literal :: TsGrammatical p => p TsLiteral TsLiteral
literal = orP
  [ only NullLiteral >? tokenOf oneP NullKeyword oneP
  , only TrueLiteral >? tokenOf oneP TrueKeyword oneP
  , only FalseLiteral >? tokenOf oneP FalseKeyword oneP
  , _TextLiteral >? textOf StringLiteral
  , _NumberLiteral >? signed NumericLiteral
  , _BigIntegerLiteral >? signed BigIntLiteral
  ]
  where
    signed :: RegGrammatical TsToken q => TsTokenCategory -> q Text Text
    signed category = orP
      [ _Negative >? tokenOf oneP MinusToken oneP >* textOf category
      , textOf category
      ]

-- | A negative number, by its spelling without its sign.
_Negative :: Prism' Text Text
_Negative = prism' ("-" <>) (Text.stripPrefix "-")

-- | A qualified name.
entityName :: TsGrammatical p => p TsEntityName TsEntityName
entityName =
  identifier >:< manyP (tokenOf oneP DotToken oneP >* identifierName)

-- | Comma separated items.
commas :: TsGrammatical p => p a a -> p [a] [a]
commas item = orP [commas1 item, _Empty >? oneP]

-- | At least one comma separated item, & a trailing comma, if it's there.
commas1 :: TsGrammatical p => p a a -> p [a] [a]
commas1 item = _Cons >? item >*< manyP (try (comma >* item))
  *< optionalToken CommaToken

comma :: TsGrammatical p => p () ()
comma = tokenOf oneP CommaToken space

-- | @...@, or not.
dots :: TsGrammatical p => p Bool Bool
dots = orP
  [ only True >? tokenOf oneP DotDotDotToken oneP
  , only False >? oneP
  ]

-- | @?@, or not.
question :: TsGrammatical p => p Bool Bool
question = orP
  [ only True >? tokenOf oneP QuestionToken oneP
  , only False >? oneP
  ]

-- | A @;@, which is printed, & parsed if it's there.
semicolon :: TsGrammatical p => p () ()
semicolon = printed (tokenOf oneP SemicolonToken oneP)

-- | A token, which is parsed if it's there, but not printed.
optionalToken :: TsGrammatical p => TsTokenCategory -> p () ()
optionalToken category = dimap (const Nothing) (const ())
  (optionalP (tokenOf oneP category oneP))

-- | Syntax, which is printed, & parsed if it's there.
printed :: TsGrammatical p => p () () -> p () ()
printed syntax = dimap (const (Just ())) (const ()) (optionalP syntax)

-- | An identifier, or a contextual keyword, by its name.
identifier :: TsGrammatical p => p Text Text
identifier = orP
  [ textOf Identifier
  , orP
      [ only text >? tokenOf oneP category oneP
      | (category, text) <- contextualKeywords
      ]
  ]

-- | An identifier, or any keyword, by its name.
identifierName :: TsGrammatical p => p Text Text
identifierName = orP
  [ identifier
  , orP
      [ only text >? tokenOf oneP category oneP
      | (category, text) <- reservedWords
      ]
  ]

-- | A tuple's element, or else an optional element's type.
_Optional :: Iso' TsType (TsType, Bool)
_Optional = iso
  (\case OptionalType node -> (node, True); node -> (node, False))
  (\case (node, True) -> OptionalType node; (node, False) -> node)

-- | An object type or a mapped type, which are braced.
_Braced :: Prism' TsType TsType
_Braced = prism' id $ \case
  node@(ObjectType _) -> Just node
  node@(MappedType {}) -> Just node
  _ -> Nothing

-- | A template's spans, by the first's type & its middle or tail.
_Spans
  :: Prism' [(TsType, Text)]
      (TsType, Either (Text, [(TsType, Text)]) Text)
_Spans = prism'
  (\case
    (node, Left (middle, others)) -> (node, middle) : others
    (node, Right tail') -> [(node, tail')])
  (\case
    [(node, tail')] -> Just (node, Right tail')
    (node, middle) : others@(_ : _) -> Just (node, Left (middle, others))
    [] -> Nothing)

-- | A template literal type without substitutions.
_NoSubstitution :: Prism' TsType Text
_NoSubstitution = prism' (`TemplateLiteralType` []) $ \case
  TemplateLiteralType text [] -> Just text
  _ -> Nothing

-- | A list of at least two, or else its only one.
_Several :: Prism' TsType [TsType] -> Iso' TsType (TsType, [TsType])
_Several nodes = iso
  (\node -> case node ^? nodes of
    Just (first : others@(_ : _)) -> (first, others)
    _ -> (node, []))
  (\case
    (node, []) -> node
    (first, others) -> review nodes (first : others))

-- | A conditional type, or else its check type.
_Conditional :: Iso' TsType (TsType, Maybe (TsType, (TsType, TsType)))
_Conditional = iso
  (\case
    ConditionalType check extends true false ->
      (check, Just (extends, (true, false)))
    node -> (node, Nothing))
  (\case
    (node, Nothing) -> node
    (check, Just (extends, (true, false))) ->
      ConditionalType check extends true false)

-- Trivia --

-- | Trivia, of whitespace & newlines, printed as some trivia.
trivia :: RegGrammatical TsToken p => [TsToken] -> p () ()
trivia shown = dimap (const shown) (const ())
  (manyP (asIn @TsToken WhitespaceTrivia >|< asIn @TsToken NewLineTrivia))

space :: RegGrammatical TsToken p => p () ()
space = trivia [TsToken WhitespaceTrivia " "]

newline :: RegGrammatical TsToken p => p () ()
newline = trivia [TsToken NewLineTrivia "\n"]

-- | A newline, indented four spaces for each depth.
indented :: RegGrammatical TsToken p => Int -> p () ()
indented depth = trivia $ TsToken NewLineTrivia "\n"
  : [TsToken WhitespaceTrivia (Text.replicate (4 * depth) " ") | depth > 0]

-- | A punctuation or keyword token, between trivia, or `oneP`.
tokenOf
  :: RegGrammatical TsToken p
  => p () () -> TsTokenCategory -> p () () -> p () ()
tokenOf before category after =
  before >* terminal [symbol category] *< after

-- | The text of a token of a category.
textOf
  :: RegGrammatical TsToken p => TsTokenCategory -> p Text Text
textOf category = iso (TsToken category) tokenText >~ asIn @TsToken category

instance CtxGrammar Char TsToken
instance Grammar Char TsToken
instance RegGrammar Char TsToken where regGrammar = tsTokenGrammar
instance CtxGrammar Char [TsToken] where ctxGrammar = tsTokensGrammar
instance CtxGrammar TsToken [TsDeclaration] where ctxGrammar = tsGrammar
