# Changelog for `distributors-grammar`

## Unreleased

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
