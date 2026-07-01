{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}

{- |
Module      : Examples.Nix
Description : A bidirectional grammar for a large core of the Nix language,
              written against the @distributors@ idioms (rule/ruleRec, the
              @>?@ \/ @>*@ \/ @*<@ \/ @>*<@ combinators, chain1, several,
              difoldl \/ difoldr).

One 'Grammar' that is simultaneously a parser and a pretty-printer. The AST is
*syntactic*, not desugared: where the Bison grammar lowers @a - b@ to
@__sub a b@ and @a < b@ to @__lessThan a b@ in its semantic actions, an
invertible grammar must keep the surface operator so that printing is the
literal inverse of parsing. Hence the 'BinOp' enum and the dedicated
'Not'/'Negate'/'HasAttr'/'Select' nodes.

RECURSION. The whole grammar is one mutual recursion. Following the
@Examples.Json@ note, every cyclic back-edge must go through a @ruleRec@ stub
(a plain @rule@ forces its body). Nix needs *two* stubs, because cyclic edges
land at two different nonterminals:

  * @expr@  — parens, antiquotation, and every body position (lambda/let/if/
              with/assert bodies, binding RHSs, formal defaults).
  * @select@ — list elements and @or@-defaults are @expr_select@, not full
               expressions (so @[ f x ]@ is two elements, not @Apply f x@).

So @nixGrammar = ruleRec "expr" $ \expr -> let sel = ruleRec "select" ... in ...@,
and the operator cascade bottoms out at the @sel@ stub. Prefix operators
(@!!x@, @- -x@) are written as a 'difoldr' over @manyP (the prefix token)@
rather than as self-reference, which would be a third forcing cycle.

WHITESPACE. Modelled in the CFG (real Nix splits this into @lexer.l@), with the
@ws@ trick from @Examples.Json@ — print-canonical, parse-liberal:
  * 'ws'  : zero-or-more whitespace, prints nothing (used next to a delimiter).
  * 'gap' : one-or-more whitespace, prints one space (used only where omitting
            it would glue two identifier-like tokens: application; after the
            keywords @if then else let in with assert inherit or rec@).
Tokenisation is ordered 'choice' + backtracking, not maximal munch: @a - b@ vs
@a -> b@ and @a < b@ vs @a <= b@ resolve by trying the longer operator first and
letting a failed right operand backtrack. This is the main structural
difference from Nix's hand-written lexer.

DELIBERATELY ELIDED (each separable): @''@-string de-indentation (a semantic
pass); the full path/URI lexicon (@\<nixpkgs\>@ search-paths collide with @\<@ and
need the lexer; @http://@ URIs are deprecated); string-escape *decoding* (kept
verbatim so the iso stays total); the "cursed or" back-compat and the
experimental @\<|@ \/ @|>@ pipes; trailing-comma edge cases in formals.

NOT COMPILED against the library in this environment; shapes are checked by hand
from the v0.6 sources. The likeliest spots needing a one-character fix are iso
*directions* (@iso f g@ vs @from@) and the tuple re-associations
('un3', 'unL3', 'binL', 'binR', 'prefixIso').
-}

module Examples.Nix
  ( Nix (..)
  , StrPart (..)
  , Binding (..)
  , Param (..)
  , Formal (..)
  , FormalItem (..)
  , Attr (..)
  , BinOp (..)
  , nixGrammar
  , nixExamples
  ) where

import Control.Applicative
import Control.Lens hiding (List)
import Control.Lens.Grammar hiding (List)

-- ---------------------------------------------------------------------------
-- Abstract syntax (syntactic, invertible)
-- ---------------------------------------------------------------------------

data Nix
  = Var String                       -- ^ identifier (incl. @true@/@false@/@null@,
                                     --   ordinary builtins in Nix, not keywords)
  | Int Integer
  | Float Double
  | Str       [StrPart]              -- ^ @"...${e}..."@
  | IndentStr [StrPart]              -- ^ @''...${e}...''@ (no de-indent modelled)
  | Path String                      -- ^ @/a@, @./a@, @~/a@
  | List    [Nix]                    -- ^ @[ e1 e2 ... ]@ (elements are selects)
  | AttrSet Bool [Binding]           -- ^ @rec?@ @{ b1; b2; ... }@
  | Lam Param Nix                    -- ^ @param: body@
  | Apply  Nix Nix                   -- ^ @f x@ (left-assoc juxtaposition)
  | Select Nix [Attr] (Maybe Nix)    -- ^ @e.a.b@ with optional @or default@
  | HasAttr Nix [Attr]               -- ^ @e ? a.b@
  | Not    Nix                       -- ^ @!e@
  | Negate Nix                       -- ^ unary @-e@
  | BinOp BinOp Nix Nix              -- ^ @l <op> r@
  | If Nix Nix Nix                   -- ^ @if c then t else f@
  | Let [Binding] Nix                -- ^ @let bs in e@
  | With   Nix Nix                   -- ^ @with e; body@
  | Assert Nix Nix                   -- ^ @assert e; body@
  deriving stock (Eq, Ord, Show, Read)

data StrPart = Lit String | Anti Nix
  deriving stock (Eq, Ord, Show, Read)

data Binding
  = BindEq [Attr] Nix                -- ^ @a.b.c = e;@
  | Inherit (Maybe Nix) [String]     -- ^ @inherit (from)? a b c;@
  deriving stock (Eq, Ord, Show, Read)

data Param
  = PVar String                      -- ^ @x:@
  | PSet [Formal] Bool               -- ^ @{ a, b ? d (, ...)? }:@  (Bool = ellipsis)
  | PSetBefore String [Formal] Bool  -- ^ @x@{ ... }:@
  | PSetAfter [Formal] Bool String   -- ^ @{ ... }@x:@
  deriving stock (Eq, Ord, Show, Read)

data Formal = Formal String (Maybe Nix)         -- ^ @name@ or @name ? default@
  deriving stock (Eq, Ord, Show, Read)

-- | Internal: a comma-separated formal-list item, either a formal or the
-- ellipsis marker. A partial iso folds @[FormalItem]@ into @([Formal],Bool)@,
-- enforcing "ellipsis last, at most once" in both directions.
data FormalItem = FFormal Formal | FEllipsis
  deriving stock (Eq, Ord, Show, Read)

data Attr
  = AStatic String                   -- ^ @a@
  | ADyn Nix                         -- ^ @${e}@
  | AStr String                      -- ^ @"a"@ (plain quoted; antiquoted form elided)
  deriving stock (Eq, Ord, Show, Read)

data BinOp
  = Impl | Or | And | Eq | Neq | Lt | Le | Gt | Ge
  | Update | Add | Sub | Mul | Div | Concat
  deriving stock (Eq, Ord, Show, Read)

makePrisms ''Nix
makePrisms ''StrPart
makePrisms ''Binding
makePrisms ''Param
makePrisms ''Formal
makePrisms ''FormalItem
makePrisms ''Attr

-- ---------------------------------------------------------------------------
-- Reserved words (excluded from variables / static attrs / formal names).
-- 'true'/'false'/'null' are intentionally NOT here: in Nix they are plain
-- identifiers resolved to builtins, so they round-trip as @Var "true"@ etc.
-- ---------------------------------------------------------------------------

keywords :: [String]
keywords = ["if","then","else","assert","with","let","in","rec","inherit","or"]

-- ---------------------------------------------------------------------------
-- Whitespace discipline
-- ---------------------------------------------------------------------------

ws :: Grammar Char ()
ws = rule "ws" $ iso (const "") (const ()) >~ manyP (oneOf " \t\r\n")

gap :: Grammar Char ()
gap = rule "gap" $ iso (const " ") (const ()) >~ someP (oneOf " \t\r\n")

sym :: String -> Grammar Char ()
sym s = ws >* terminal s *< ws

comma :: Grammar Char ()
comma = sym ","

-- ---------------------------------------------------------------------------
-- Lexical rules
-- ---------------------------------------------------------------------------

identStart, identCont :: Grammar Char Char
identStart = asIn @Char LowercaseLetter <|> asIn @Char UppercaseLetter <|> token @Char '_'
identCont  = identStart <|> asIn @Char DecimalNumber <|> token @Char '\'' <|> token @Char '-'

-- | Raw identifier @[A-Za-z_][A-Za-z0-9_'-]*@.
ident :: Grammar Char String
ident = rule "ident" $ identStart >:< manyP identCont

-- | Identifier that is not a reserved word. 'satisfied' is the bidirectional
-- guard: rejects keywords on parse, rejects a malformed @Var "let"@ on print.
identifier :: Grammar Char String
identifier = rule "identifier" $ satisfied (`notElem` keywords) >? ident

intG :: Grammar Char Nix
intG = rule "int" $ _Int . iso show read >? someP (asIn @Char DecimalNumber)

-- | Simplified float. @show/read \@Double@ is not a true iso (e.g. @1.0@ vs
-- @1@ do not both round-trip): the one knowingly-lossy literal.
floatG :: Grammar Char Nix
floatG = rule "float" $
  _Float . iso show read >? someP (asIn @Char DecimalNumber <|> token @Char '.')

pathG :: Grammar Char Nix
pathG = rule "path" $ _Path >? (oneOf "/.~" >:< someP pathChar)
  where
    pathChar =
          asIn @Char LowercaseLetter <|> asIn @Char UppercaseLetter
      <|> asIn @Char DecimalNumber  <|> oneOf "/._-+"

-- | @"...${e}..."@. Antiquotation is a full expression; literal runs are
-- maximal (no two adjacent 'Lit'); escapes are kept verbatim.
stringG :: Grammar Char Nix -> Grammar Char Nix
stringG e = rule "string" $
  _Str >? (terminal "\"" >* manyP part *< terminal "\"")
  where
    part   = (_Anti >? antiquote e) <|> (_Lit >? someP chr)
    chr    = notOneOf "\"\\$" <|> (terminal "\\" >* anyToken)

-- | @''...${e}...''@. Indentation preserved verbatim (de-indent elided).
indentStringG :: Grammar Char Nix -> Grammar Char Nix
indentStringG e = rule "indent-string" $
  _IndentStr >? (terminal "''" >* manyP part *< terminal "''")
  where
    part = (_Anti >? antiquote e) <|> (_Lit >? someP (notOneOf "'$"))

antiquote :: Grammar Char Nix -> Grammar Char Nix
antiquote e = terminal "${" >* ws >* e *< ws *< terminal "}"

-- ---------------------------------------------------------------------------
-- Re-associations: makePrisms gives N-tuples; >*< builds right-nested pairs.
-- ---------------------------------------------------------------------------

un3 :: Iso' (a, b, c) (a, (b, c))
un3 = iso (\(a,b,c) -> (a,(b,c))) (\(a,(b,c)) -> (a,b,c))

unL3 :: Iso' (a, b, c) ((a, b), c)
unL3 = iso (\(a,b,c) -> ((a,b),c)) (\((a,b),c) -> (a,b,c))

-- | @BinOp o l r  <->  (l,(o,r))@   (left-fold shape)
binL :: Iso' (BinOp, Nix, Nix) (Nix, (BinOp, Nix))
binL = iso (\(o,l,r) -> (l,(o,r))) (\(l,(o,r)) -> (o,l,r))

-- | @BinOp o l r  <->  ((l,o),r)@   (right-fold shape)
binR :: Iso' (BinOp, Nix, Nix) ((Nix, BinOp), Nix)
binR = iso (\(o,l,r) -> ((l,o),r)) (\((l,o),r) -> (o,l,r))

-- | inner focus of a unary node @Not e@ / @Negate e@ reshaped for difoldr,
-- where a prefix occurrence carries no payload: @e <-> ((), e)@.
prefixIso :: Iso' Nix ((), Nix)
prefixIso = iso (\n -> ((), n)) (\((), n) -> n)

-- ---------------------------------------------------------------------------
-- Operator-precedence cascade helpers.
--
-- chain1 bakes in a *single* fixed binary constructor (cf. Examples.Arithmetic),
-- which is perfect for one-operator levels. Nix has levels with several
-- operators of equal precedence (@+ -@, @* /@, the comparisons), so the folded
-- element is a *pair* (BinOp, operand) and the step iso (binL/binR) threads the
-- operator into the AST. difoldl/difoldr then collapse @(head,[(op,arg)])@
-- exactly as chain1 does internally -- the one genuinely interesting bit.
-- ---------------------------------------------------------------------------

binTok :: BinOp -> String -> Grammar Char BinOp
binTok v s = only v >? sym s

infixlG :: Grammar Char BinOp -> Grammar Char Nix -> Grammar Char Nix
infixlG op sub = difoldl (_BinOp . binL) >? (sub >*< manyP (op >*< sub))

infixrG :: Grammar Char BinOp -> Grammar Char Nix -> Grammar Char Nix
infixrG op sub = difoldr (_BinOp . binR) >? (manyP (sub >*< op) >*< sub)

nonAssocG :: Grammar Char BinOp -> Grammar Char Nix -> Grammar Char Nix
nonAssocG op sub = (_BinOp . binL >? (sub >*< op >*< sub)) <|> sub

-- prefix run: @op* sub@ folded right into nested unary nodes (n=0 -> just sub).
prefixG :: APrism' Nix Nix -> String -> Grammar Char Nix -> Grammar Char Nix
prefixG ctor s sub = difoldr (clonePrism ctor . prefixIso) >? (manyP (sym s) >*< sub)

-- ---------------------------------------------------------------------------
-- The grammar. Two recursion knots: `expr` (top) and `sel` (select level).
-- ---------------------------------------------------------------------------

nixGrammar :: Grammar Char Nix
nixGrammar = ruleRec "expr" $ \expr ->
  let sel = ruleRec "select" (selectG expr)
  in choice
       [ lambdaG expr
       , letG expr
       , ifG expr
       , withG expr
       , assertG expr
       , cascade expr sel
       ]

-- Operator cascade, lowest -> highest, mirroring the Bison %prec table:
--   -> | || | && | == != | < <= > >= | // | ! | + - | * / | ++ | ? | -unary
-- It captures both stubs: `expr` (for dynamic attrs / parens deep inside) and
-- `sel` (the application/select bottom).
cascade :: Grammar Char Nix -> Grammar Char Nix -> Grammar Char Nix
cascade expr sel = implG
  where
    implG    = rule "impl"    $ infixrG (binTok Impl "->") orG
    orG      = rule "or"      $ infixlG (binTok Or   "||") andG
    andG     = rule "and"     $ infixlG (binTok And  "&&") eqG
    eqG      = rule "eq"      $ nonAssocG (binTok Eq "==" <|> binTok Neq "!=") cmpG
    cmpG     = rule "cmp"     $
      nonAssocG (choice [binTok Le "<=", binTok Ge ">=", binTok Lt "<", binTok Gt ">"]) updateG
    updateG  = rule "update"  $ infixrG (binTok Update "//") notG
    notG     = rule "not"     $ prefixG _Not "!" addG
    addG     = rule "add"     $ infixlG (binTok Add "+" <|> binTok Sub "-") mulG
    mulG     = rule "mul"     $ infixlG (binTok Mul "*" <|> binTok Div "/") concatG
    concatG  = rule "concat"  $ infixrG (binTok Concat "++") hasAttrG
    hasAttrG = rule "hasattr" $
      (_HasAttr >? (negG >*< (sym "?" >* attrPath expr))) <|> negG
    negG     = rule "negate"  $ prefixG _Negate "-" appG
    appG     = rule "apply"   $ chain1 Left _Apply (sepBy gap) sel

-- e.a.b (or default)? | atom.  Uses `expr` for parens/dynamic attrs and the
-- `select` self-stub for the `or`-default and (via atomG) for list elements.
selectG :: Grammar Char Nix -> Grammar Char Nix -> Grammar Char Nix
selectG expr select =
      (_Select . un3 >? ( atomG expr select
                      >*< (ws >* terminal "." >* ws >* attrPath expr)
                      >*< optionalP (gap >* terminal "or" >* gap >* select) ))
  <|> atomG expr select

atomG :: Grammar Char Nix -> Grammar Char Nix -> Grammar Char Nix
atomG expr select = rule "atom" $ choice
  [ terminal "(" >* ws >* expr *< ws *< terminal ")"
  , _List >? (terminal "[" >* ws >* several (sepBy gap) select *< ws *< terminal "]")
  , attrSetG expr
  , floatG                 -- before intG: 3.14 must not parse as (Int 3) then .14
  , intG
  , stringG expr
  , indentStringG expr
  , pathG
  , _Var >? identifier
  ]

-- ---------------------------------------------------------------------------
-- Attribute paths and attributes
-- ---------------------------------------------------------------------------

attrPath :: Grammar Char Nix -> Grammar Char [Attr]
attrPath e = rule "attrpath" $ several1 (sepBy (ws >* terminal "." *< ws)) (attrG e)

attrG :: Grammar Char Nix -> Grammar Char Attr
attrG e = rule "attr" $ choice
  [ _AStatic >? identifier
  , _ADyn    >? antiquote e
  , _AStr    >? (terminal "\"" >* manyP (notOneOf "\"") *< terminal "\"")
  ]

-- ---------------------------------------------------------------------------
-- Bindings, attribute sets
-- ---------------------------------------------------------------------------

attrSetG :: Grammar Char Nix -> Grammar Char Nix
attrSetG e = rule "attrset" $
  _AttrSet >? (recFlag >*< (terminal "{" >* ws >* manyP (bindingG e *< ws) *< terminal "}"))
  where
    recFlag :: Grammar Char Bool
    recFlag = iso (\b -> if b then Just () else Nothing) (maybe False (const True))
              >~ optionalP (terminal "rec" *< gap)

bindingG :: Grammar Char Nix -> Grammar Char Binding
bindingG e = rule "binding" $ (bindEq <|> bindInherit) *< ws *< terminal ";"
  where
    bindEq = _BindEq >? (attrPath e >*< (sym "=" >* e))
    bindInherit = _Inherit >?
      ( terminal "inherit"
        >* optionalP (ws >* terminal "(" >* ws >* e *< ws *< terminal ")")
       >*< manyP (gap >* identifier) )

-- ---------------------------------------------------------------------------
-- Lambdas, parameter patterns, formals
-- ---------------------------------------------------------------------------

lambdaG :: Grammar Char Nix -> Grammar Char Nix
lambdaG e = rule "lambda" $ _Lam >? (paramG e *< ws *< terminal ":" *< ws >*< e)

-- @-forms tried before bare PVar; each fails fast at a distinguishing token.
paramG :: Grammar Char Nix -> Grammar Char Param
paramG e = rule "param" $ choice
  [ _PSetBefore . un3  >? (identifier *< sym "@" >*< setCore e)
  , _PSetAfter  . unL3 >? (setCore e >*< (sym "@" >* identifier))
  , _PSet              >? setCore e
  , _PVar              >? identifier
  ]

setCore :: Grammar Char Nix -> Grammar Char ([Formal], Bool)
setCore e = terminal "{" >* ws >* formalsG e *< ws *< terminal "}"

formalsG :: Grammar Char Nix -> Grammar Char ([Formal], Bool)
formalsG e = fold >? several (sepBy comma) (formalItemG e)
  where
    fold = partialIso
      (\(fs, ell) -> Just (map FFormal fs ++ [FEllipsis | ell]))
      (go [])
    go acc = \case
      []                 -> Just (reverse acc, False)
      [FEllipsis]        -> Just (reverse acc, True)
      (FFormal f : rest) -> go (f : acc) rest
      (FEllipsis : _)    -> Nothing            -- ellipsis not last

formalItemG :: Grammar Char Nix -> Grammar Char FormalItem
formalItemG e = (_FFormal >? formalG e) <|> (_FEllipsis >? terminal "...")

formalG :: Grammar Char Nix -> Grammar Char Formal
formalG e = rule "formal" $ _Formal >? (identifier >*< optionalP (sym "?" >* e))

-- ---------------------------------------------------------------------------
-- if / let / with / assert
-- ---------------------------------------------------------------------------

ifG :: Grammar Char Nix -> Grammar Char Nix
ifG e = rule "if" $
  _If . un3 >? ( (terminal "if" >* gap >* e)
             >*< (gap >* terminal "then" >* gap >* e)
             >*< (gap >* terminal "else" >* gap >* e) )

letG :: Grammar Char Nix -> Grammar Char Nix
letG e = rule "let" $
  _Let >? ( (terminal "let" >* gap >* manyP (bindingG e *< ws))
        >*< (ws >* terminal "in" >* gap >* e) )

withG :: Grammar Char Nix -> Grammar Char Nix
withG e = rule "with" $
  _With >? ((terminal "with" >* gap >* e *< sym ";") >*< e)

assertG :: Grammar Char Nix -> Grammar Char Nix
assertG e = rule "assert" $
  _Assert >? ((terminal "assert" >* gap >* e *< sym ";") >*< e)

-- ---------------------------------------------------------------------------
-- Round-trip examples (text is the canonical printed form: ws prints empty,
-- gap prints one space; the parser also accepts more liberal whitespace).
-- ---------------------------------------------------------------------------

nixExamples :: [(Nix, String)]
nixExamples =
  [ (Var "x", "x")
  , (Var "true", "true")                                     -- builtin, not a keyword
  , (Int 42, "42")
  , (Negate (Int 42), "-42")
  , (Not (Var "b"), "!b")
  , (BinOp Add (Int 1) (Int 2), "1+2")
  , (BinOp Add (BinOp Mul (Int 2) (Int 3)) (Int 4), "2*3+4")
  , (BinOp Mul (Int 2) (BinOp Add (Int 3) (Int 4)), "2*(3+4)")
  , (Apply (Var "f") (Var "x"), "f x")
  , (Apply (Apply (Var "f") (Var "x")) (Var "y"), "f x y")
  , (Lam (PVar "x") (Var "x"), "x:x")
  , (Lam (PSet [Formal "a" Nothing, Formal "b" (Just (Int 1))] True) (Var "a"), "{a,b?1,...}:a")
  , (Lam (PSetAfter [Formal "a" Nothing] False "args") (Var "args"), "{a}@args:args")
  , (Select (Var "x") [AStatic "y", AStatic "z"] Nothing, "x.y.z")
  , (Select (Var "x") [AStatic "y"] (Just (Int 0)), "x.y or 0")
  , (HasAttr (Var "x") [AStatic "y"], "x?y")
  , (AttrSet False [BindEq [AStatic "a"] (Int 1), BindEq [AStatic "b"] (Int 2)], "{a=1;b=2;}")
  , (AttrSet True [BindEq [AStatic "a"] (Int 1)], "rec {a=1;}")
  , (AttrSet False [Inherit Nothing ["a", "b"]], "{inherit a b;}")
  , (AttrSet False [Inherit (Just (Var "pkgs")) ["lib"]], "{inherit (pkgs) lib;}")
  , (List [Int 1, Int 2, Int 3], "[1 2 3]")
  , (List [Var "f", Var "x"], "[f x]")                       -- two elements, not Apply
  , (List [], "[]")
  , (If (Var "c") (Int 1) (Int 2), "if c then 1 else 2")
  , (Let [BindEq [AStatic "x"] (Int 1)] (Var "x"), "let x=1; in x")
  , (With (Var "pkgs") (Var "lib"), "with pkgs;lib")
  , (Assert (BinOp Eq (Var "x") (Int 1)) (Var "x"), "assert x==1;x")
  , (BinOp Impl (Var "a") (BinOp And (Var "b") (Var "c")), "a->b&&c")
  , (BinOp Update (AttrSet False []) (AttrSet False [BindEq [AStatic "a"] (Int 1)]), "{}//{a=1;}")
  ]
  