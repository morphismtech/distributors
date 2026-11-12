# Changelog for `distributors`

## Unreleased

### New APIs

- `Enumerable`, in `Data.Traversable.Homogeneous`, of `Homogeneous`
  countable sums of single copies, sequenced `enumerably` by
  `CocartesianMonoidal`s, with generic defaults by `Generic1`.
- `Comonocle`s, in `Control.Lens.Comonocle`, dual to `Monocle`s by sums:
  `comonocle`, `_Enumerable`, `_BoundedEnum`, & concrete
  `Comonocular`s, with `runComonocular`.
- `WrappedPafb f p` is `CocartesianMonoidal` for any `Functor f`.
- `AComonocle`, `withComonocle`, `cloneComonocle`, `mapComonocle`,
  `altComonocle`, `crossComonocle`, `indexComonocle` &
  `zipWithComonocle`; & `crossMonocle`.
- `Ditraversal`s, a secondary concrete representation of `Monocle`s,
  by `Traversable` & `Distributive` homogeneous products,
  with `ditraversal` & `withDitraversal`.
- Enum-like optics & functions of `Enumerable`s: the prism
  `fromEnumerable`, the partial isos `succEnumerable` & `predEnumerable`,
  `enumerateFrom`, `enumerateFromThen`, `enumerateFromTo` &
  `enumerateFromThenTo`; & of `Comonocle`s: the prism `fromComonocle`,
  the partial isos `succComonocle` & `predComonocle`, `enumerateComonocle`,
  `enumerateFromThenComonocle`, `enumerateFromToComonocle` &
  `enumerateFromThenToComonocle`.
- `Homogeneous` & `Enumerable` instances for `Down`, `Min`, `Max`,
  `First`, `Last`, `Alt f`, `Ap f` & `IdentityT f`.
- `Homogeneous` & `Enumerable` instances for `(,) e`, a copy for each tag
  of a `Bounded` `Enum`, summed in a balanced tree.

### Bug Fixes

- `Grating` is `Profunctor` & `Closed`, so every `Grate`, & so every
  `Monocle`, is `AGrate`, for `withGrate`, `cotraverseOf` & co.

### Breaking Changes

- `Enumerable`, its functions & `Indexing`, renamed `Enumerator`, move from
  `Data.Traversable.Homogeneous` to `Data.Traversable.Homogeneous.Enumerable`.
- `Comonocle`s & their combinators move from `Control.Lens.Monocle` to
  their own module, `Control.Lens.Comonocle`.
- `Data.Profunctor.Separator` merges into `Data.Profunctor.Distributor`:
  `SepBy`, `several`, `chain`, `intercalateP`, `withOperators` & so on.
- The grammars move to their own package, `distributors-grammar`:
  `Control.Lens.Grammar` & its `BackusNaur`, `Machine`, `RegEx`, `Symbol`
  & `Token` modules, `Control.Monad.Fail.Try`, `Data.Profunctor.Grammar`
  & `Data.Profunctor.Grammar.Parsector`. So `distributors` no longer
  depends on `QuickCheck`, `random`, `MemoTrie`, `monad-loops` or `mtl`.
- `Control.Lens.Grammar.Internal.NestedPrismTH` & `.Orphanage` are renamed
  `Control.Lens.Internal.Distributor.NestedPrismTH` & `.Orphanage`.
- `Operator`'s `Infix`, `Prefix` & `Postfix` take `APrism`s, rather than
  `APartialIso`s, so that `withOperators` builds every operator it parses,
  rather than failing by `error`, or dropping prefix & postfix operators.
- `MonadicTry` moves from `Data.Profunctor.Monadic` to
  `Control.Monad.Fail.Try`, which `Data.Profunctor.Monadic` no longer
  imports, & `Data.Profunctor.Monadic` no longer re-exports `try`.
- `sepWith`, `beginWith` & `endWith` move from `Data.Profunctor.Separator`
  to `Control.Lens.Grammar.Symbol`, beside `terminal`, so that
  `Data.Profunctor.Separator` needn't import grammar symbols.

## 0.6.0.0 - 2026-04-24

### New Module

- Added `Control.Lens.Grammar.Machine` as the transducer/matching runtime layer.

### New Types

- Added `Transducer` and `TransducerStep` as the finite-state representation for
  compiled grammar machines.

### New APIs (Machine Runtime)

- Added `transducer` to compile `Bnf (RegEx token)` into `Transducer`.
- Added `parseForest` to reconstruct parse forests with rule labels and token spans/slices,
  returning the remaining unparsed suffix.
- Added `expectNext` to compute scanner-frontier expected token classes after a prefix.
- Added `languageSample` to lazily enumerate sampled language words from shortest length upward.
- Added `unreachableRules` to report dead nonterminals unreachable from the start expression.

### Internal Machinery

- Implemented Thompson-style transducer construction over `RegEx`-extended BNF.
- Implemented Earley-style chart runtime (`initialChart`, `closeChartAt`, `scanClassOptions`,
  `prefixGen`) with predict/complete closure and scanner grouping.
- Added completion-time caller indexing/cache optimizations and precomputed rule nullability/first-state
  indexing to speed machine execution.

### Grammar Integration

- `Control.Lens.Grammar` now exposes machine-backed generators:
  `transducerG` and the parse-forest examples/docs built on the Machine runtime.

## 0.5.0.0 - 2026-04-16

### Changes

- `MonadTry` now implies `BackusNaurForm` (so `rule` tracing/failure semantics are available)
  and `Filtrator` (via `MonadPlus`, with `filtrate = mfiltrate`).
- Simplified the default implementation of `terminal`.
- Added `applicativeG` and `monadG` generators via `Joker` orphan and non-orphan instances.
- Made nomenclature consistent with use of "fail" and "failure", not "error".

### Internal

- Moved orphan instances and Template Haskell internals to `Control.Lens.Grammar.Internal`.

### Documentation

- Expanded `BackusNaurForm` documentation with separate motivation from:
  category-theoretic structure and failure-tracing semantics (both called “trace”
  in different senses, and combined by BNF-style rules).
- Added a `monadG` Megaparsec example.
- Fixed typo in the `makeNestedPrisms` example.

## 0.4.0.0 - 2026-04-10

### New Modules

- `Control.Monad.Fail.Try` - `MonadTry` class with `try` & `fail` for backtracking parsers
- `Data.Profunctor.Grammar.Parsector` - Invertible LL(1) parser with Parsec-style failure reporting:
  `ParsecState`, `ParsecFailure`, `parsecP`, `unparsecP`; implements hints, LL(1) commitment
  via `parsecLooked`, and `try` for explicit backtracking
- `Data.Profunctor.Separator` - Separator/delimiter combinators: `sepWith`, `noSep`,
  `beginWith`, `endWith`, `several`, `several1`, `intercalateP`, `chain`, `chain1`
- `Data.Traversable.Homogeneous` - `Homogeneous` class for static containers with uniform elements;
  `ditraverse` for distributive traversals

### New Combinators

- `Control.Lens.Grammar.Kleene`: `tokenClass` embedding into `RegEx`; `KleeneAlgebra` laws
  as QuickCheck properties; `RegExam` helpers `failExam`, `passExam`, `isFailExam`
- `Control.Lens.Grammar.Boole`: `trueB`, `falseB` added to `BooleanAlgebra`;
  `andB`, `orB`, `allB`, `anyB` fold combinators
- `Data.Profunctor.Monadic`: `MonadicTry` constraint alias; `P.return` combinator;
  improved documentation for qualified do-notation pattern bonding
- `Data.Profunctor.Distributor`: `manyP` / `optionalP` now place the empty case on
  the right of `>+<` for correct LL(1) behaviour (`p >*< manyP p >+< oneP`)

### Changes

- `<|>` in `Parsector` now commits when the left branch consumes input (LL(1));
  use `try` to opt into backtracking
- `TokenTest` renamed to `TokenClass` throughout
- `chain`, `chain1`, `intercalateP` moved from `Data.Profunctor.Distributor`
  to the new `Data.Profunctor.Separator`
- `BackusNaurForm`: `rule` documentation clarified; added reference to Breitner's
  *Showcasing Applicative*

### Testing

- `test/Properties/Kleene` - QuickCheck properties for `KleeneStarAlgebra`,
  `TokenAlgebra`, `BooleanAlgebra TokenClass`
- `test/Examples/Chain` - Chain grammar example
- `test/Main`: `testCtxGrammarExample` extended with `parsecG` / `unparsecG` round-trip checks

## 0.3.0.0 - 2026-02-05

### New Modules

- `Control.Lens.Grammar` - Grammar hierarchy based on Chomsky's formal grammar classification
- `Control.Lens.Grammar.BackusNaur` - Context-free grammar combinators (BNF)
- `Control.Lens.Grammar.Boole` - Boolean algebra for grammars
- `Control.Lens.Grammar.Kleene` - Regular expression combinators
- `Control.Lens.Grammar.Symbol` - Symbol-level grammar primitives
- `Control.Lens.Grammar.Token` - Token-level grammar primitives
- `Data.Profunctor.Filtrator` - Filterable profunctors
- `Data.Profunctor.Grammar` - Grammar profunctor abstraction
- `Data.Profunctor.Monadic` - Monadic profunctor combinators with QualifiedDo support
- `Data.Profunctor.Monoidal` - Monoidal profunctor combinators

### Removed Modules

- `Text.Grammar.Distributor` - Functionality split into the new modules above

### Testing

- Added `doctest` for documentation testing
- New test examples: Arithmetic, Json, Lambda, LenVec, RegString, SemVer, SExpr

## 0.2.0.0 - 2025-07-08

Added some combinators for `RegEx`es. Updated documentation.

## 0.1.0.0

First version with profunctorial interpretation of invertible syntax.

