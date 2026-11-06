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

Both layers are @LL(1)@, since `tsTokensGrammar` scans tokens without
their trivia, so that `parsecG` parses & `unparsecG` prints each layer,
locating failures. Here, a declaration prints as tokens, & as characters,
& parses back.

>>> :set -XOverloadedStrings
>>> let point = ObjectType [PropertySignature (PropertyIdentifier "x") False (KeywordType NumberKeyword)]
>>> let printed = unparsecG tsGrammar [TypeAliasDeclaration True "Point" point] ([] :: [TsToken])
>>> let source = parsecStream (unparsecG tsTokensGrammar (parsecStream printed) ("" :: String))
>>> putStr source
export type Point = { x: number };
>>> parsecResult (parsecG tsGrammar (concat (parsecResult (parsecG tsTokensGrammar source))))
Just [TypeAliasDeclaration True "Point" (ObjectType [PropertySignature (PropertyIdentifier "x") False (KeywordType NumberKeyword)])]
>>> let scanned = concat (parsecResult (parsecG tsTokensGrammar "type A = { a: number; b: };"))
>>> parsecOffset (parsecG tsGrammar scanned)
10
-}

module Control.Lens.Grammar.TypeScript
  ( -- * Syntax
    TsDeclaration (..)
  , TsType (..)
  , TsProperty (..)
  , TsPropertyName (..)
  , TsLiteral (..)
  , tsGrammar
    -- * Tokens
  , TsToken (..)
  , TsTokenCategory (..)
  , tsTokenGrammar
  , tsTokensGrammar
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
data TsDeclaration = TypeAliasDeclaration Bool Text TsType
  deriving stock (Eq, Ord, Show, Read)

-- | A type, by the TypeScript compiler's name of its node.
data TsType
  = KeywordType TsTokenCategory -- ^ @number@, @string@, @never@, …
  | LiteralType TsLiteral -- ^ @null@, @true@ or @"abc"@
  | TypeReference Text [TsType] -- ^ @T@ or @T\<U, V>@
  | ArrayType TsType -- ^ @T[]@
  | TupleType [TsType] -- ^ @[T, U]@
  | OptionalType TsType -- ^ @T?@, an element of a tuple
  | RestType TsType -- ^ @...T@, an element of a tuple
  | UnionType [TsType] -- ^ @T | U@
  | IntersectionType [TsType] -- ^ @T & U@
  | ParenthesizedType TsType -- ^ @(T)@
  | ObjectType [TsProperty] -- ^ @{ x: T; y?: U }@
  | MappedType Text TsType (Maybe TsType) Bool TsType
  -- ^ @{ [k in K as L]?: T }@, with a name type & an optional token or not
  | ConditionalType TsType TsType TsType TsType
  -- ^ @T extends U ? V : W@
  | TemplateLiteralType Text [(TsType, Text)]
  -- ^ @\`a${T}b\`@, by its head & its spans' types & literals
  deriving stock (Eq, Ord, Show, Read)

-- | A member of an `ObjectType`.
data TsProperty
  = PropertySignature TsPropertyName Bool TsType
  -- ^ @x: T@ or @x?: T@
  | IndexSignature Text TsType TsType -- ^ @[k: K]: T@
  deriving stock (Eq, Ord, Show, Read)

-- | The name of a `PropertySignature`.
data TsPropertyName
  = PropertyIdentifier Text -- ^ @x@
  | PropertyString Text -- ^ @"x y"@
  deriving stock (Eq, Ord, Show, Read)

-- | A literal of a `LiteralType`.
data TsLiteral
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
makeNestedPrisms ''TsType
makeNestedPrisms ''TsProperty
makeNestedPrisms ''TsPropertyName
makeNestedPrisms ''TsLiteral

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
so that @`manyP` tsTokenGrammar@ scans a file, or `tsTokensGrammar`
scans it without its trivia.

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

{- | Tokens, scanned from their characters without their trivia,
as the TypeScript compiler's scanner skips trivia, & printed with them,
as `tsGrammar` prints them, so that `tsGrammar` parses by @LL(1)@.
-}
tsTokensGrammar :: RegGrammar Char [TsToken]
tsTokensGrammar = rmap
  (\scanned -> [t | t <- scanned, tokenCategory t `notElem` trivial])
  (manyP tsTokenGrammar)
  where
    trivial = [WhitespaceTrivia, NewLineTrivia]

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

Trivia, whitespace & newlines, are printed conventionally, between tokens,
& parsed only by `parseG`, from tokens with trivia, since `parsecG`
parses tokens without them, which `tsTokensGrammar` scans.
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
      , _TemplateLiteralType >? textOf TemplateHead *< tight
          >*< templateSpans ty
      , _TypeReference >? identifier >*< orP
          [ several1 (sepBy comma)
              { beginBy = tokenOf tight LessThanToken tight
              , endBy = tokenOf tight GreaterThanToken oneP
              } ty
          , only [] >? oneP
          ]
      , _TupleType >? tokenOf oneP OpenBracketToken oneP >* orP
          [ only [] >? tokenOf tight CloseBracketToken oneP
          , tight >* several1 (sepBy comma) (tupleElement ty)
              *< tokenOf tight CloseBracketToken oneP
          ]
      , _ParenthesizedType >? tokenOf oneP OpenParenToken tight
          >* ty *< tokenOf tight CloseParenToken oneP
      , _Braced >? tokenOf oneP OpenBraceToken oneP >* orP
          [ only (ObjectType []) >? tokenOf tight CloseBraceToken oneP
          , _Bracketed >? tokenOf space OpenBracketToken tight >* identifier
              >*< (mappedRest ty >+< indexRest ty)
          , _PropertyFirst >? space >* property ty >*< members ty
          ]
      ]
    -- The rest of a mapped type, after its type parameter's name.
    mappedRest ty = tokenOf space InKeyword space >* ty
      >*< optionalP (tokenOf space AsKeyword space >* ty)
      >*< tokenOf tight CloseBracketToken oneP >* question
      >*< tokenOf tight ColonToken space >* ty
      *< tokenOf space CloseBraceToken oneP
    -- The rest of a type literal, after its first index signature's name.
    indexRest ty = tokenOf tight ColonToken space >* ty
      >*< tokenOf tight CloseBracketToken oneP
      >* tokenOf tight ColonToken space >* ty
      >*< members ty
    -- The members after a type literal's first, & its closing brace.
    members ty = ruleRec "members" $ \rest -> orP
      [ only [] >? tokenOf space CloseBraceToken oneP
      , tokenOf tight SemicolonToken space >* orP
          [ only [] >? tokenOf tight CloseBraceToken oneP
          , member ty >:< rest
          ]
      ]
    -- A template's spans, each a type & its middle's or tail's literal.
    templateSpans ty = ruleRec "spans" $ \rest -> _Spans >? ty
      >*< (tight >* textOf TemplateMiddle *< tight >*< rest
        >+< tight >* textOf TemplateTail)
    tupleElement ty = rule "element" $ orP
      [ _RestType >? tokenOf oneP DotDotDotToken tight >* ty
      , _Optional >~ ty >*< question
      ]
    member ty = rule "member" $ orP
      [ _PropertySignature >? property ty
      , _IndexSignature >? tokenOf oneP OpenBracketToken tight >* identifier
          >*< indexSignature ty
      ]
    property ty = propertyName >*< question
      >*< tokenOf tight ColonToken space >* ty
    indexSignature ty = tokenOf tight ColonToken space >* ty
      >*< tokenOf tight CloseBracketToken oneP
      >* tokenOf tight ColonToken space >* ty
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
  :: Prism' TsType [TsType] -> Iso' TsType (TsType, [TsType])
_Several nodes = iso
  (\node -> case node ^? nodes of
    Just (first : others@(_ : _)) -> (first, others)
    _ -> (node, []))
  (\case
    (node, []) -> node
    (first, others) -> review nodes (first : others))

-- | A type literal or a mapped type, which are braced.
_Braced :: Prism' TsType TsType
_Braced = prism' id $ \case
  node@(ObjectType _) -> Just node
  node@(MappedType {}) -> Just node
  _ -> Nothing

-- | A tuple's element, or else an optional element's type.
_Optional :: Iso' TsType (TsType, Bool)
_Optional = iso
  (\case OptionalType node -> (node, True); node -> (node, False))
  (\case (node, True) -> OptionalType node; (node, False) -> node)

{- | A mapped type, or a type literal whose first member is an index
signature, by its type parameter's or index's name, & the rest of it.
-}
_Bracketed :: Prism' TsType
  ( Text
  , Either
      (TsType, (Maybe TsType, (Bool, TsType)))
      (TsType, (TsType, [TsProperty]))
  )
_Bracketed = prism' bracketed $ \case
  MappedType name constraint nameType optional node ->
    Just (name, Left (constraint, (nameType, (optional, node))))
  ObjectType (IndexSignature name key node : others) ->
    Just (name, Right (key, (node, others)))
  _ -> Nothing
  where
    bracketed = \case
      (name, Left (constraint, (nameType, (optional, node)))) ->
        MappedType name constraint nameType optional node
      (name, Right (key, (node, others))) ->
        ObjectType (IndexSignature name key node : others)

-- | A type literal whose first member is a property signature.
_PropertyFirst
  :: Prism' TsType ((TsPropertyName, (Bool, TsType)), [TsProperty])
_PropertyFirst = prism'
  (\((name, (optional, node)), others) ->
    ObjectType (PropertySignature name optional node : others))
  (\case
    ObjectType (PropertySignature name optional node : others) ->
      Just ((name, (optional, node)), others)
    _ -> Nothing)

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

-- | A type of any arrays of its element type.
_Arrays :: Iso' TsType (TsType, [()])
_Arrays = iso arrays (uncurry (foldr (const ArrayType)))
  where
    arrays = \case
      ArrayType node -> (() :) <$> arrays node
      node -> (node, [])

-- | A conditional type, or else its check type.
_Conditional
  :: Iso' TsType (TsType, Maybe (TsType, (TsType, TsType)))
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
_NoSubstitution :: Prism' TsType Text
_NoSubstitution = prism' (`TemplateLiteralType` []) $ \case
  TemplateLiteralType text [] -> Just text
  _ -> Nothing
