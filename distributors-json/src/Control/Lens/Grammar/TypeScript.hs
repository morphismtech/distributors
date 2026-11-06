{-# LANGUAGE OverloadedStrings #-}

{- |
Module      : Control.Lens.Grammar.TypeScript
Description : TypeScript type declarations, as a grammar
Copyright   : (C) 2026 - Eitan Chatav
License     : BSD-style (see the file LICENSE)
Maintainer  : Eitan Chatav <eitan.chatav@gmail.com>
Stability   : provisional
Portability : non-portable

The type declarations of TypeScript, like the TypeScript compiler,
in two layers: a `tsTokenGrammar` of its tokens, by their `TsTokenCategory`s,
& a `tsGrammar` of its syntax, of those tokens, by the compiler's
names of its nodes, so that they parse & print together.

>>> :set -XOverloadedStrings
>>> let point = TypeLiteral [PropertySignature (PropertyIdentifier "x") False (KeywordType NumberKeyword)]
>>> mapM_ putStr (tsPrint [TypeAliasDeclaration True "Point" point])
export type Point = { x: number };

>>> tsParse "type Pair = [string, number?];"
Just [TypeAliasDeclaration False "Pair" (TupleType [KeywordType StringKeyword,OptionalType (KeywordType NumberKeyword)])]
-}

module Control.Lens.Grammar.TypeScript
  ( -- * Syntax
    TsDeclaration (..)
  , TypeNode (..)
  , TypeElement (..)
  , PropertyName (..)
  , Literal (..)
  , tsGrammar
    -- * Tokens
  , TsToken (..)
  , TsTokenCategory (..)
  , tsTokenGrammar
    -- * Text
  , tsPrint
  , tsParse
  ) where

import Control.Lens
import Control.Lens.Grammar
import Data.Char (chr, ord)
import Data.Maybe (fromMaybe, listToMaybe)
import Data.Text (Text)
import Data.Text qualified as Text
import Numeric (readHex, showHex)

-- Syntax --

-- | A type alias, @export type T = U;@, exported or not.
data TsDeclaration = TypeAliasDeclaration Bool Text TypeNode
  deriving stock (Eq, Ord, Show, Read)

-- | A type, by the TypeScript compiler's name of its node.
data TypeNode
  = KeywordType TsTokenCategory -- ^ @number@, @string@, @never@, …
  | LiteralType Literal -- ^ @null@, @true@ or @"abc"@
  | TypeReference Text [TypeNode] -- ^ @T@ or @T\<U, V>@
  | ArrayType TypeNode -- ^ @T[]@
  | TupleType [TypeNode] -- ^ @[T, U]@
  | OptionalType TypeNode -- ^ @T?@, an element of a tuple
  | RestType TypeNode -- ^ @...T@, an element of a tuple
  | UnionType [TypeNode] -- ^ @T | U@
  | IntersectionType [TypeNode] -- ^ @T & U@
  | ParenthesizedType TypeNode -- ^ @(T)@
  | TypeLiteral [TypeElement] -- ^ @{ x: T; y?: U }@
  | MappedType Text TypeNode (Maybe TypeNode) Bool TypeNode
  -- ^ @{ [k in K as L]?: T }@, with a name type & an optional token or not
  | ConditionalType TypeNode TypeNode TypeNode TypeNode
  -- ^ @T extends U ? V : W@
  | TemplateLiteralType Text [(TypeNode, Text)]
  -- ^ @\`a${T}b\`@, by its head & its spans' types & literals
  deriving stock (Eq, Ord, Show, Read)

-- | A member of a `TypeLiteral`.
data TypeElement
  = PropertySignature PropertyName Bool TypeNode
  -- ^ @x: T@ or @x?: T@
  | IndexSignature Text TypeNode TypeNode -- ^ @[k: K]: T@
  deriving stock (Eq, Ord, Show, Read)

-- | The name of a `PropertySignature`.
data PropertyName
  = PropertyIdentifier Text -- ^ @x@
  | PropertyString Text -- ^ @"x y"@
  deriving stock (Eq, Ord, Show, Read)

-- | A literal of a `LiteralType`.
data Literal
  = NullLiteral -- ^ @null@
  | TrueLiteral -- ^ @true@
  | FalseLiteral -- ^ @false@
  | TextLiteral Text -- ^ @"abc"@
  deriving stock (Eq, Ord, Show, Read)

-- Tokens --

{- | A token, of a `TsTokenCategory` & its text, as the scanner of
the TypeScript compiler scans it, with its trivia: its text is
an identifier's name, a string's value or a template's literal.
-}
data TsToken = TsToken
  { tokenCategory :: TsTokenCategory
  , tokenText :: Text
  } deriving stock (Eq, Ord, Show, Read)

instance Categorized TsToken where
  type Categorize TsToken = TsTokenCategory
  categorize = tokenCategory

-- | The kinds of `TsToken`s, by the TypeScript compiler's names.
data TsTokenCategory
  = WhitespaceTrivia
  | NewLineTrivia
  | Identifier
  | StringLiteral
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
  | DotDotDotToken
  | SemicolonToken
  | CommaToken
  | LessThanToken
  | GreaterThanToken
  | QuestionToken
  | ColonToken
  | EqualsToken
  | BarToken
  | AmpersandToken
  | AnyKeyword
  | AsKeyword
  | BigIntKeyword
  | BooleanKeyword
  | ExportKeyword
  | ExtendsKeyword
  | FalseKeyword
  | InKeyword
  | KeyOfKeyword
  | NeverKeyword
  | NullKeyword
  | NumberKeyword
  | ObjectKeyword
  | ReadonlyKeyword
  | StringKeyword
  | SymbolKeyword
  | TrueKeyword
  | TypeKeyword
  | UndefinedKeyword
  | UnknownKeyword
  | VoidKeyword
  deriving stock (Eq, Ord, Show, Read, Enum, Bounded)

makeNestedPrisms ''TsDeclaration
makeNestedPrisms ''TypeNode
makeNestedPrisms ''TypeElement
makeNestedPrisms ''PropertyName
makeNestedPrisms ''Literal

-- | The text of a punctuation or keyword `TsTokenCategory`.
kindText :: TsTokenCategory -> Maybe Text
kindText = flip lookup ((CloseBraceToken, "}") : punctuation <> keywords)

punctuation :: [(TsTokenCategory, Text)]
punctuation =
  [ (OpenBraceToken, "{"), (OpenParenToken, "("), (CloseParenToken, ")")
  , (OpenBracketToken, "["), (CloseBracketToken, "]")
  , (DotDotDotToken, "..."), (SemicolonToken, ";"), (CommaToken, ",")
  , (LessThanToken, "<"), (GreaterThanToken, ">"), (QuestionToken, "?")
  , (ColonToken, ":"), (EqualsToken, "="), (BarToken, "|")
  , (AmpersandToken, "&")
  ]

keywords :: [(TsTokenCategory, Text)]
keywords =
  [ (AnyKeyword, "any"), (AsKeyword, "as"), (BigIntKeyword, "bigint")
  , (BooleanKeyword, "boolean"), (ExportKeyword, "export")
  , (ExtendsKeyword, "extends"), (FalseKeyword, "false"), (InKeyword, "in")
  , (KeyOfKeyword, "keyof"), (NeverKeyword, "never"), (NullKeyword, "null")
  , (NumberKeyword, "number"), (ObjectKeyword, "object")
  , (ReadonlyKeyword, "readonly"), (StringKeyword, "string")
  , (SymbolKeyword, "symbol"), (TrueKeyword, "true"), (TypeKeyword, "type")
  , (UndefinedKeyword, "undefined"), (UnknownKeyword, "unknown")
  , (VoidKeyword, "void")
  ]

-- | The token of a punctuation or keyword `TsTokenCategory`.
symbol :: TsTokenCategory -> TsToken
symbol kind = TsToken kind (fromMaybe "" (kindText kind))

{- | A token, scanned from its characters. Its trivia are tokens,
as the scanner of the TypeScript compiler scans without skipping them,
so that @`manyP` tsTokenGrammar@ scans a file.

Unlike the compiler's scanner, which rescans a @}@ as a template's
middle or tail, by the context of its parser, `tsTokenGrammar` is regular,
so that a @}@ followed by @\`@ or @${@ is a template's tail or middle,
of an empty literal, as it always is in a type.
-}
tsTokenGrammar :: RegGrammar Char TsToken
tsTokenGrammar = orP
  [ kindOf WhitespaceTrivia >? someP (oneOf @Char (" \t" :: String))
  , kindOf NewLineTrivia >? orP
      [only "\n" >? terminal "\n", only "\r\n" >? terminal "\r\n"]
  , _Word >? identifierStart >:< manyP identifierPart
  , kindOf StringLiteral >? terminal "\"" >* manyP stringChar *< terminal "\""
  , _Template >? terminal "`" >* manyP templateChar >*< orP
      [ only NoSubstitutionTemplateLiteral >? terminal "`"
      , only TemplateHead >? terminal "${"
      ]
  , _Closing >? terminal "}" >* orP
      [ only TemplateTail >? terminal "`"
      , only TemplateMiddle >? terminal "${"
      , only CloseBraceToken >? oneP
      ]
  , orP
      [ only (TsToken kind text) >? terminal (Text.unpack text)
      | (kind, text) <- punctuation
      ]
  ]
  where
    identifierStart = orP
      [ asIn @Char UppercaseLetter, asIn @Char LowercaseLetter
      , asIn @Char TitlecaseLetter
      , asIn @Char ModifierLetter, asIn @Char OtherLetter
      , asIn @Char LetterNumber
      , oneOf @Char ("_$" :: String)
      ]
    identifierPart = orP
      [ identifierStart, asIn @Char DecimalNumber, asIn @Char NonSpacingMark
      , asIn @Char SpacingCombiningMark, asIn @Char ConnectorPunctuation
      ]
    stringChar = orP
      [ notOneOf @Char ('"' : '\\' : ['\0' .. '\31'])
      , terminal "\\" >* orP
          [ oneOf @Char ("\"\\/" :: String)
          , only '\b' >? terminal "b", only '\f' >? terminal "f"
          , only '\n' >? terminal "n", only '\r' >? terminal "r"
          , only '\t' >? terminal "t"
          , terminal "u" >* (_HexCode >? replicateP 4 (oneOf @Char hexDigits))
          ]
      ]
    hexDigits = "0123456789abcdefABCDEF" :: String
    templateChar = orP
      [ notOneOf @Char ("`$\\" :: String)
      , terminal "\\" >* oneOf @Char ("`$\\" :: String)
      ]

-- | A token of a kind, by its text.
kindOf :: TsTokenCategory -> Prism' TsToken String
kindOf kind = prism'
  (TsToken kind . Text.pack)
  (\(TsToken kind' text) ->
    if kind == kind' then Just (Text.unpack text) else Nothing)

-- | An identifier or keyword, by its text.
_Word :: Prism' TsToken String
_Word = prism' word $ \(TsToken kind text) ->
  if kind == Identifier || kind `elem` map fst keywords
    then Just (Text.unpack text) else Nothing
  where
    word chars = case lookup text [(t, k) | (k, t) <- keywords] of
      Just kind -> TsToken kind text
      Nothing -> TsToken Identifier text
      where
        text = Text.pack chars

-- | A template without substitutions, or a template's head.
_Template :: Prism' TsToken (String, TsTokenCategory)
_Template = prism'
  (\(chars, kind) -> TsToken kind (Text.pack chars))
  (\(TsToken kind text) ->
    if kind `elem` [NoSubstitutionTemplateLiteral, TemplateHead]
      then Just (Text.unpack text, kind) else Nothing)

-- | A @}@, or a template's middle or tail, of an empty literal.
_Closing :: Prism' TsToken TsTokenCategory
_Closing = prism'
  (\kind -> TsToken kind (if kind == CloseBraceToken then "}" else ""))
  (\case
    TsToken CloseBraceToken "}" -> Just CloseBraceToken
    TsToken TemplateMiddle "" -> Just TemplateMiddle
    TsToken TemplateTail "" -> Just TemplateTail
    _ -> Nothing)

-- | A character, by the hexadecimal digits of a @\\u@ escape.
_HexCode :: Prism' Char String
_HexCode = prism'
  (\digits -> chr (maybe 0 fst (listToMaybe (readHex digits))))
  (\c -> if ord c < 0x10000
    then Just (pad (showHex (ord c) "")) else Nothing)
  where
    pad digits = replicate (4 - length digits) '0' <> digits

-- Syntax --

{- | Type declarations, of tokens, by the TypeScript compiler's syntax.

Trivia, whitespace & newlines, are parsed between tokens, & printed
conventionally. Each run of trivia is the trivia of exactly one token,
either before or after it, so that it parses only one way.
-}
tsGrammar :: Grammar TsToken [TsDeclaration]
tsGrammar = rule "declarations" $
  trivia [] >* manyP declaration
  where
    declaration = rule "declaration" $ _TypeAliasDeclaration
      >? exported
      >*< identifier
      >*< tokenOf space EqualsToken space >* typeNode
      *< tokenOf tight SemicolonToken newline
    exported = orP
      [ only True >? tokenOf oneP ExportKeyword space
          >* tokenOf oneP TypeKeyword space
      , only False >? tokenOf oneP TypeKeyword space
      ]
    typeNode = ruleRec "type" $ \ty -> _Conditional
      >~ unionType ty >*< optionalP
        ( tokenOf space ExtendsKeyword space >* unionType ty
          >*< tokenOf space QuestionToken space >* ty
          >*< tokenOf space ColonToken space >* ty
        )
    unionType ty = rule "union" $ _Several _UnionType
      >~ leading BarToken >* intersectionType ty >*< manyP
        (tokenOf space BarToken space >* intersectionType ty)
    intersectionType ty = rule "intersection" $ _Several _IntersectionType
      >~ leading AmpersandToken >* postfixType ty >*< manyP
        (tokenOf space AmpersandToken space >* postfixType ty)
    -- A leading operator, which is parsed but not printed.
    leading kind = dimap (const Nothing) (const ())
      (optionalP (tokenOf oneP kind space))
    postfixType ty = rule "postfix" $ _Arrays
      >~ primaryType ty >*< manyP
        ( tokenOf tight OpenBracketToken oneP
          >* tokenOf tight CloseBracketToken oneP
        )
    primaryType ty = rule "primary" $ orP
      [ _KeywordType >? orP
          [ only kind >? tokenOf oneP kind oneP
          | kind <-
            [ AnyKeyword, BigIntKeyword, BooleanKeyword, NeverKeyword
            , NumberKeyword, ObjectKeyword, StringKeyword, SymbolKeyword
            , UndefinedKeyword, UnknownKeyword, VoidKeyword
            ]
          ]
      , _LiteralType >? orP
          [ only NullLiteral >? tokenOf oneP NullKeyword oneP
          , only TrueLiteral >? tokenOf oneP TrueKeyword oneP
          , only FalseLiteral >? tokenOf oneP FalseKeyword oneP
          , _TextLiteral >? textOf StringLiteral
          ]
      , _NoSubstitution >? textOf NoSubstitutionTemplateLiteral
      , _TemplateLiteralType >? textOf TemplateHead *< trivia [] >*<
          (_Snoc >? manyP (templateSpan TemplateMiddle (trivia []))
            >*< templateSpan TemplateTail oneP)
      , _TypeReference >? identifier >*< orP
          [ only [] >? oneP
          , tokenOf tight LessThanToken tight
              >* several1 (sepBy comma) ty
              *< tokenOf tight GreaterThanToken oneP
          ]
      , _TupleType >? orP
          [ only [] >? tokenOf oneP OpenBracketToken oneP
              >* tokenOf tight CloseBracketToken oneP
          , tokenOf oneP OpenBracketToken tight
              >* several1 (sepBy comma) (tupleElement ty)
              *< tokenOf tight CloseBracketToken oneP
          ]
      , _ParenthesizedType >? tokenOf oneP OpenParenToken tight
          >* ty *< tokenOf tight CloseParenToken oneP
      , _TypeLiteral >? orP
          [ only [] >? tokenOf oneP OpenBraceToken oneP
              >* tokenOf tight CloseBraceToken oneP
          , tokenOf oneP OpenBraceToken space
              >* several1 (sepBy semicolon) (member ty)
              *< optionalSemicolon
              *< tokenOf space CloseBraceToken oneP
          ]
      , _MappedType >? tokenOf oneP OpenBraceToken space
          >* tokenOf oneP OpenBracketToken tight >* identifier
          >*< tokenOf space InKeyword space >* ty
          >*< optionalP (tokenOf space AsKeyword space >* ty)
          >*< tokenOf tight CloseBracketToken oneP >* question
          >*< tokenOf tight ColonToken space >* ty
          *< tokenOf space CloseBraceToken oneP
      ]
      where
        templateSpan kind after =
          ty >*< trivia [] >* textOf kind *< after
    tupleElement ty = rule "element" $ orP
      [ _RestType >? tokenOf oneP DotDotDotToken tight >* ty
      , _OptionalType >? ty *< tokenOf tight QuestionToken oneP
      , ty
      ]
    member ty = rule "member" $ orP
      [ _PropertySignature >? propertyName >*< question
          >*< tokenOf tight ColonToken space >* ty
      , _IndexSignature >? tokenOf oneP OpenBracketToken tight >* identifier
          >*< tokenOf tight ColonToken space >* ty
          >*< tokenOf tight CloseBracketToken oneP
          >* tokenOf tight ColonToken space >* ty
      ]
    propertyName = orP
      [ _PropertyIdentifier >? identifier
      , _PropertyIdentifier >? orP
          [only text >? tokenOf oneP kind oneP | (kind, text) <- keywords]
      , _PropertyString >? textOf StringLiteral
      ]
    question = orP
      [ only True >? tokenOf tight QuestionToken oneP
      , only False >? oneP
      ]
    comma = tokenOf tight CommaToken space
    semicolon = tokenOf tight SemicolonToken space
    optionalSemicolon = dimap (const Nothing) (const ())
      (optionalP (tokenOf tight SemicolonToken oneP))
    identifier = textOf Identifier
    space = trivia [TsToken WhitespaceTrivia " "]
    newline = trivia [TsToken NewLineTrivia "\n"]
    tight = trivia []

{- | Trivia, of any whitespace & newlines, printed as some trivia. -}
trivia
  :: (Lexical TsToken p, Alternator p)
  => [TsToken] -> p () ()
trivia printed = dimap (const printed) (const ())
  (manyP (asIn @TsToken WhitespaceTrivia >|< asIn @TsToken NewLineTrivia))

-- | A punctuation or keyword token, between trivia, or `oneP`.
tokenOf
  :: (Lexical TsToken p, Alternator p)
  => p () () -> TsTokenCategory -> p () () -> p () ()
tokenOf before kind after = before >* terminal [symbol kind] *< after

-- | The text of a token of a kind.
textOf :: (Lexical TsToken p, Alternator p) => TsTokenCategory -> p Text Text
textOf kind = iso (TsToken kind) tokenText >~ asIn @TsToken kind

-- | A list of at least two, or else its only one.
_Several
  :: Prism' TypeNode [TypeNode] -> Iso' TypeNode (TypeNode, [TypeNode])
_Several nodes = iso
  (\node -> case node ^? nodes of
    Just (first : others@(_ : _)) -> (first, others)
    _ -> (node, []))
  (\case
    (node, []) -> node
    (first, others) -> review nodes (first : others))

-- | A type of any arrays of its element type.
_Arrays :: Iso' TypeNode (TypeNode, [()])
_Arrays = iso arrays (uncurry (foldr (const ArrayType)))
  where
    arrays = \case
      ArrayType node -> (() :) <$> arrays node
      node -> (node, [])

-- | A conditional type, or else its check type.
_Conditional
  :: Iso' TypeNode (TypeNode, Maybe (TypeNode, (TypeNode, TypeNode)))
_Conditional = iso
  (\case
    ConditionalType check extends true false ->
      (check, Just (extends, (true, false)))
    node -> (node, Nothing))
  (\case
    (node, Nothing) -> node
    (check, Just (extends, (true, false))) ->
      ConditionalType check extends true false)

-- | A template literal type without substitutions.
_NoSubstitution :: Prism' TypeNode Text
_NoSubstitution = prism' (`TemplateLiteralType` []) $ \case
  TemplateLiteralType text [] -> Just text
  _ -> Nothing

-- Text --

{- | Print type declarations, by `tsGrammar` & `tsTokenGrammar`,
or `Nothing` for syntax that they don't print, like an unparenthesized
union type within an array type.
-}
tsPrint :: [TsDeclaration] -> Maybe String
tsPrint declarations = do
  printed <- ($ []) <$> printG tsGrammar declarations
  ($ "") <$> printG (manyP tsTokenGrammar) printed

-- | Parse type declarations, by `tsTokenGrammar` & `tsGrammar`.
tsParse :: String -> Maybe [TsDeclaration]
tsParse source = do
  let scanned = parsecG (manyP tsTokenGrammar) source
  scannedTokens <- parsecResult scanned
  if null (parsecStream scanned)
    then listToMaybe
      [parsed | (parsed, []) <- parseG tsGrammar scannedTokens]
    else Nothing
