# Changelog for `distributors-grammar`

## Unreleased

- `ruleTyped`, in `Control.Lens.Grammar.BackusNaur`, a `rule` named by its
  `Typeable` type, module-qualified, which was `distributors-json`'s
  `jsonTyped`. Base types' grammars name their rules by it.
- Regular expressions escape control characters by hexadecimal codes,
  @\\x{e}@, rather than by names, which were ambiguous, @\\SO@ & @H@
  reading as @\\SOH@; codes parse in either case.
- `digit` & `numeral`, digits & natural numbers in a base, by their values,
  rather than by `show` & `read`, which `Natural` & `Integer` grammars,
  quantifiers' counts, & the examples use.
- `regexGrammar` & `regbnfGrammar` are removed: they're the `Grammar Char`
  instances of `RegEx Char` & `Bnf (RegEx Char)`, by `grammar`. The classes
  `RegGrammar`, `Grammar` & `CtxGrammar`, & the base types' instances, are
  in `Control.Lens.Grammar.Class`, which `Control.Lens.Grammar` re-exports,
  so that `Control.Lens.Grammar.RegEx` defines its own instances; their
  tutorials are `Control.Lens.Grammar`'s module documentation.
- `RegEx` has counts, a `KleeneTimes` constructor, normalized by `timesK`,
  rendered @x{n}@, @x{n,}@ & @x{n,m}@, & parsed so, normalizing; `Grammor`s
  keep counts, so `exactly`, `atLeast`, `atMost` & `inRange` render by them.
  Machines & analyses unroll them.
- `RegEx` records `try`, by a `Backtracking` constructor, whose language
  is its own, rendered @\\t{…}@; `ll1Conflicts` skips conflicts resolved
  by `try`. `Tried` is part of `RegGrammatical`.
- Character classes render runs of three or more plain characters as
  ranges, @[a-z]@, & parse ranges; a dash in a class is escaped, @\\-@.
- Grammars of base types, each a rule named by its type by `ruleTyped`,
  with parity with their `Read` & `Show` instances' lexemes, printing as
  `show` does & parsing as `read` does, but for the whitespace &
  parentheses which `read` accepts around any lexeme: `Char` literals, with
  `showLitChar`'s escapes, & `read`'s named, numeric & control escapes;
  `Natural`, `Integer`, & sized `Int`s & `Word`s, which wrap out of range
  as `read` does, in decimal, & binary, octal & hexadecimal; & `Double`s
  & `Float`s, by `floatToDigits` & `fromRational`. They're regular & LL(1).
  `String`, a list of characters, has no instance.
- `Predicate`s are `Tokenized` & `TokenAlgebra`s, as predicates are; &
  `ReadPrec` runs grammars as `ReadP` does, `Tokenized`, a `TokenAlgebra`,
  `TerminalSymbol`, `Ruled`, `BackusNaurForm` & `Tried`.
- `Control.Lens.Grammar.Analysis`, static analyses of `RegEx`tended
  t'Bnf's over any token: `foldRegEx`, the homomorphism out of `RegEx`, the
  free `KleeneStarAlgebra` of token classes & nonterminals, & `fixRules`,
  least fixpoints over a t'Bnf''s `bnfRules`; `Leading`, nullability &
  leading atoms, by which `firsts` & `leftRecursive`; `Guard`, a
  `BooleanAlgebra` of one-token lookahead, by which `follows`; &
  `ll1Conflicts`, built of them, testing each example's @LL(1)@ flag.
  The lambda example's abstraction rule is renamed, as it shared its name
  with the grammar's, merging into a left-recursive rule.
- `RegString` & `RegBnf` are removed: `RegEx Char` & `Bnf (RegEx Char)`
  are them, `IsString` & `IsList` by the string syntax of regular
  expressions, of `regexGrammar` & `regbnfGrammar`, & their `Grammar Char`
  instances, while their `Show` & `Read` are stock; render them by
  `toList` or `putStringLn`. `regstringG` is renamed `regexG`, & `regexG`
  & `regbnfG` generate over any token, `RegEx token` & `Bnf (RegEx token)`.
- Modules, without orphans: `Control.Lens.Grammar.BackusNaur` has `Ruled`,
  `BackusNaurForm` & `Tried`, & the `RegGrammatical`, `Grammatical` &
  `CtxGrammatical` constraints, `Lexical` being folded into
  `RegGrammatical`, of which it was always a part; `Control.Lens.Grammar.RegEx`
  has `RegEx` & `Bnf`, with `liftBnf0`, `liftBnf1`, `liftBnf2` & `diffB`,
  & `regexGrammar` & `regbnfGrammar`; & `Printor` has its own module,
  `Data.Profunctor.Grammar.Printor`, re-exported by
  `Data.Profunctor.Grammar`. `Control.Lens.Grammar` re-exports them all.
- `Control.Monad.Fail.Try`, with `MonadTry` & `MonadicTry`, is removed.
  `Control.Lens.Grammar.BackusNaur` has, instead:
  - `Ruled`, with `rule`, split from `BackusNaurForm`, now its subclass,
    whose `ruleRec` defaults to @ruleRec label = rule label . fix@, so
    that its invariant holds for any `rule`;
  - `failP`, renamed from `failBnf`, for any `Ruled` `DisjunctiveMonoid`;
  - `Tried`, with `try`, for any grammar, not only monads, defaulting to
    `id`, as `try` doesn't change a language. `Parsector` backtracks by
    it, a t'Bnf' tries its start, & a `RegEx` doesn't record it, for now.

  `Grammatical` requires `Tried`, so context-free grammars can `try`, &
  `CtxGrammatical` requires `MonadPlus` & `MonadFail` of `Filtrator`s.
  `Control.Lens.Grammar` still re-exports `Alternative`, `MonadPlus`,
  `MonadFail` & `Filterable`.
- `RegGrammar`, `Grammar` & `CtxGrammar` are classes, of a type's
  grammar over a token, by `regGrammar`, `grammar` & `ctxGrammar`, each
  defaulting to the more restrictive, & `RegGrammatical`, `Grammatical`
  & `CtxGrammatical` are the constraints on profunctors which run them,
  typing grammar values, as @Grammatical Char p => p a a@. Runners take
  the grammar from the class: parsers & printers by inference, as
  @parseG \@Arith@, & generators by a required type argument, as
  @regbnfG Arith@, or @regbnfG (type SemVer)@ where a constructor shares
  the type's name. Run a grammar value by the backends' own runners,
  `parseP`, `printP`, `parsecP` & co.
- Token classes test their sets of tokens logarithmically, by `Set`, in
  `tokenClass`'s default & in `oneOf` & `notOneOf` of predicates, rather
  than linearly by `Foldable`: parsing the JSON example, whose characters
  are a class of over a million tokens, is hundreds of times faster.
- `Control.Lens.Grammar` re-exports `Control.Lens.Bifocal`, for `>?<*`,
  which applies `Bifocal`s in `CtxGrammar`s, as they're `Filtrator`s.
- `Parsor`'s `manyP` & `optionalP` parse & print their elements in turn,
  rather than by `Distributor`'s defaults, through isomorphisms & sums:
  parsing repetitions is ~40% faster, & the test examples 10-50%.
- `unparseG` & `unparsecG` document that printing `snoc`s, so a `String`
  prints quadratically, & a `Data.Sequence.Seq` linearly.
- Benchmarks, `bench:core`, of `distributors`' combinators & the test
  examples, at parsing, printing & `Parsector`.
- The grammars of `distributors` 0.6, split into their own package:
  `Control.Lens.Grammar` & its `BackusNaur`, `Machine`, `RegEx`, `Symbol`
  & `Token` modules, `Control.Monad.Fail.Try`, `Data.Profunctor.Grammar`
  & `Data.Profunctor.Grammar.Parsector`.
- `Control.Lens.Grammar` re-exports `Control.Lens.Prismoid` &
  `Control.Lens.Diopter`, so grammars separate by `sepBy`, of
  `several`, `atLeast`, `chain1` & `exactly`, & `Control.Lens.Grammar.Symbol`
  exports `sepWith`, `sepBy` of a `terminal` separator, delimiters
  composing around a separated grammar by `>*` & `*<`.
- `Printor s` & `Parsor s` are `MonadicTrans`, so `Varifocal`s run on
  them, as the heredoc example grammar does; `Control.Lens.Grammar`
  re-exports `Control.Lens.Varifocal` &
  `Data.Profunctor.Monadic`.
- `Grammor` defines `manyTillP` as @starK p <> q@, without recursing, so
  `sepBy` grammars, even of shapes without foci, have finite
  regular expressions & `Bnf`s.
- `RegExam`, the type, is renamed `TokenExam`, & moves with `TokenClass`,
  `TokenAlgebra` & `CategoryTest` to `Control.Lens.Grammar.Token`;
  `RegEx`'s `RegExam` constructor keeps its name. `foldTokenClass` folds a
  `TokenClass` by an algebra of its `TokenExam`s.
- `RegEx`'s `Sequence` & `TokenExam`'s `Alternate` take two or more items,
  as two & a list, normalized,
  so that `RegEx`'s `Monoid` & `DisjunctiveMonoid`, & `TokenClass`'s
  `DisjunctiveMonoid`, are associative up to `==`, as tested; regular
  expressions print with fewer parentheses.
