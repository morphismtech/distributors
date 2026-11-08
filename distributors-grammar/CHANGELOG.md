# Changelog for `distributors-grammar`

## Unreleased

- The grammars of `distributors` 0.6, split into their own package:
  `Control.Lens.Grammar` & its `BackusNaur`, `Machine`, `RegEx`, `Symbol`
  & `Token` modules, `Control.Monad.Fail.Try`, `Data.Profunctor.Grammar`
  & `Data.Profunctor.Grammar.Parsector`.
- `RegExam`, the type, is renamed `TokenExam`, & moves with `TokenClass`,
  `TokenAlgebra` & `CategoryTest` to `Control.Lens.Grammar.Token`;
  `RegEx`'s `RegExam` constructor keeps its name. `foldTokenClass` folds a
  `TokenClass` by an algebra of its `TokenExam`s.
- `RegEx`'s `Sequence` & `TokenExam`'s `Alternate` take two or more items,
  as two & a list, normalized,
  so that `RegEx`'s `Monoid` & `DisjunctiveMonoid`, & `TokenClass`'s
  `DisjunctiveMonoid`, are associative up to `==`, as tested; regular
  expressions print with fewer parentheses.
