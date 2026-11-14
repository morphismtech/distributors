# Changelog for `distributors`

## Unreleased

### New APIs

- `stepping` & its combinators, `terminateBy`, `delimitBy`, `balanceBy`
  & `countWith`, step through any stream, @(Cons s s a a, AsEmpty s)@,
  like a `Data.Sequence.Seq` or `Data.Text.Text`, not only lists.
- `Enumerable`, in `Data.Traversable.Homogeneous`, of `Homogeneous`
  countable sums of single copies, sequenced `enumerably` by
  `CocartesianMonoidal`s, with generic defaults by `Generic1`.
- `Comonocle`s, in `Control.Lens.Comonocle`, dual to `Monocle`s by sums:
  `comonocle`, `_Enumerable`, `_BoundedEnum`, & concrete
  `Comonocular`s, with `runComonocular`.
- `WrappedPafb f p` is `CocartesianMonoidal` for any `Functor f`.
- `AComonocle`, `withComonocle`, `cloneComonocle`, `mapComonocle`,
  `altComonocle`, `alongsideComonocle`, `indexComonocle` &
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
  of a `Bounded` `Enum`, summed in a balanceBy tree.
- A `Homogeneous` instance for `NonEmpty`.
- Dual combinators: `copiesComonocle`, the `Prism`s of a `Comonocle`'s
  copies, exactly one of which matches, & `fociMonocle`, the `Lens`es of
  a `Monocle`'s foci, every one of which focuses.
- `Prismoid`s move to their own module, `Control.Lens.Prismoid`, from
  `Control.Lens.Bifocal`, with `opted`, `lefted`, `righted`, `chain1` &
  `chain`; & new `exactly`, `atLeast`, `atMost` & `inRange`.
- `sepBy sep pat p`, running any `Prismoid` with a separator between
  consecutive foci, by the `Alternator`'s own `manyP`, `someP`,
  `optionalP` & `optionP`, preferring foci, greedily; so
  `sepBy sep several`, `sepBy sep (atLeast 1)`, `sepBy sep (chain1 assoc pat)`
  & `sepBy sep (exactly n)` sequence lists, binary constructor
  patterns & repetitions, separated. Delimiters compose around it.
- `Varifocal`s, in `Control.Lens.Varifocal`, context-sensitive optics
  whose shape may depend on the foci they build: `Bifocal` ⊂ `Varifocal`,
  their `Applicative` the monad of a `MonadicTrans` profunctor, absorbed
  by `joinP`; with `Varifocal'`; the applicators `contextually`, in any
  `Monadic` `Alternator`, like a `CtxGrammar`, by its free concrete form
  `Varifocus`, & `contextuallyT`, on a `MonadicTrans` profunctor;
  `AVarifocal`, `varifocus`, `runVarifocus`, `runVarifocusT` &
  `cloneVarifocal`; `crossVarifocal`, `altVarifocal`, `orVarifocal`
  & `bindVarifocal`,
  the last choosing a second by what the first built, like a netstring; & `stepping`, a deterministic machine over foci,
  deciding by each built whether to continue, stop or reject, with its
  instances `terminateBy`, `delimitBy`, `balanceBy` & `countWith`:
  sentinel-terminated, matching-delimitBy, nested & count-prefixed
  sequences, which no `Bifocal` can express.
- Combinators of optics with the same foci: `crossPrismoid`,
  `crossBifocal`, `crossDiopter` & `crossGrate`, on pairs; `altPrismoid`,
  `altBifocal` & `altDiopter`, on `Either`s; & `orPrismoid` & `orBifocal`,
  disjoining two on the same source by `>|<`, with the units
  `oneOptic`, `zeroOptic` & `falseOptic`, of the crosses, alts & ors,
  by inclusion, of every optic which has them.
- `MonadicTrans`, in `Data.Profunctor.Monadic`, profunctors transforming a
  monad, lifting its effects by `liftP` & absorbing them by `joinP`.
- `skipManyP` & `skipOptionalP`, zero or more, & zero or one, skipped:
  sequencing actions forwards & none backwards, like whitespace or a
  trailing separator, which a parser accepts & a printer omits; & their
  `Diopter`s, `skippedMany` & `skippedOptional`.
- `inRange lo hi`, a `Prismoid` of between some numbers of times, at least
  @lo@ & at most @hi@, if @Just@, like a regular expression's @{lo,hi}@ or
  @{lo,}@; & its intervals `exactly`, `atLeast` & `atMost`.
- `listed`, in `Control.Lens.PartialIso`, a list of items as an `IsList`,
  `iso fromList toList`: act on an `IsList` as on lists by `listed ~< p`.
- `manyTillP`, an `Alternator` method, zero or more, then the rest,
  @p* q@, trying the rest first, like parsec's @manyTill@, which a static
  `Alternator` defines without recursing, as @starK p <> q@.
- `>?*`, the action of a `Prismoid` on `Alternator`s, applying it directly,
  without a concrete form, so the `Alternator`'s own methods act.
- `Prismatoid`, the concrete form of `Prismoid`s, a partial `Dioptrice`,
  with `APrismoid`, `prismoid`, `withPrismoid`, `clonePrismoid` &
  `runPrismatoid`.
- Secondary concrete representations: `Prismocular`s of `Prismoid`s,
  probing by `Alternative`s, with `runPrismocular`, `prismocular` &
  `withPrismocular`; `Spectacle`s of `Bifocal`s, by `Homogeneous`
  shapes with partial merges, with `runSpectacle`, `spectacle` &
  `withSpectacle`; & `Diffraction`s of `Grate`s, by `Distributive`
  shapes, with `diffraction` & `withDiffraction`.
- `lengthPrepend`, in `Data.Profunctor.Monadic`, a count, then that many
  repetitions, which depend on the count built.
- `satisfied` is a homomorphism of predicates' `BooleanAlgebra`s, to the
  `DisjunctiveMonoid` of partial functions, choosing by first success in
  either direction, by which `withOperators` tries its unary operators.
- `genericNestedPrism` & `genericNestedIso`, in `Control.Lens.Prism.Nested`
  & re-exported by `Control.Lens.PartialIso`, the `Prism`s & `Iso`s that
  `makeNestedPrisms` generates, focusing fields as right-nested pairs,
  by `GHC.Generics` rather than Template Haskell, taking the type, &
  for a `Prism` the constructor's name as a `Symbol`, as required type
  arguments, like @genericNestedPrism Shape "Rect"@; a type sharing its
  constructor's name is @(type Point)@, by @ExplicitNamespaces@.
- `orPartialIso`, the union of two patterns, trying the first, then the
  second, in either direction, with its unit `falsePartialIso`.

### Performance

- `exactly`, `atLeast`, `atMost` & `inRange` sequence their foci at the
  target itself, & its `Applicative` once: 25-34% faster printing &
  Parsector parsing of counted repetitions.
- `withOperators` prints left-associated chains in linear time, not
  quadratic.
- `Distributor`'s default `manyP` ties its knot, building its action once.

### Bug Fixes

- `Grating` is `Profunctor` & `Closed`, so every `Grate`, & so every
  `Monocle`, is `AGrate`, for `withGrate`, `cotraverseOf` & co.

### Breaking Changes

- `mapBifocal` is replaced by `>?<*`, `Bifocal`'s applicator, which
  applies a `Bifocal` directly at a partial `Alternator`, keeping its own
  methods, like `optionP`, as `>?*` does a `Prismoid`'s, & ~25% faster
  than through a `Spectacle`. Apply `ABifocal` by `cloneBifocal`.
- `Control.Lens.Internal.Distributor.NestedPrismTH` is renamed
  `Control.Lens.Prism.Nested`.
- `crossPartialIso` ~> `alongsidePartialIso` & `altPartialIso` ~>
  `withoutPartialIso`, after lens's `alongside` & `without`, since they
  pair & sum differing foci, unlike the crosses & alts of the same foci.
- `withoutPartialIso` & `alongsidePartialIso` keep a `Prism`'s passing a mismatch
  through, a pair only where both components pass through.
- `>?<` passes a mismatch through by `Choice`, as `>?` does, so a
  `Prism` acts by `>?<` as by `>?`.
- `PartialExchange` is removed. `APartialIso` is by `PartialMarket`s,
  so `clonePartialIso` is the identity, keeping a `Prism`'s passing a
  mismatch through; `withPartialIso pattern partialIso` rebuilds a
  `PartialIso` from its partial functions, failing on a mismatch instead.
- `Bifocal`s need `(Alternator p, Applicative f, Filterable f)`, dropping
  `Filtrator p` & `Alternative f`, which `Filterable f` provides, as it
  does `PartialIso`'s `Cochoice`.
- `ABifocal` is by `Spectacle`s, matching shapes once, rather than by
  `Binocular`s, whose probes rematch from the source, quadratically, &
  unroll repetition, so `cloneBifocal` & `mapBifocal` of repeating
  `Bifocal`s like `atLeast 1` diverged at static `Profunctor`s.
- The `base` lower bound is 4.20 (GHC 9.10).
- `Prismoid`s need `(Alternator p, Applicative f)`, rather than an
  `Alternative f`, failing by their `Alternator` alone, so that they have
  a concrete form, `Prismatoid`.
- `Witheroid` & `witherPrism` are removed: a `Witheroid`'s `Alternative f`
  could fail backwards, without a concrete form, & `witherPrism` is
  `clonePartialIso`, with `catMaybes (pure Nothing)` for `empty`, as
  `withered`'s documentation shows.

- `imprism` & the orphan `Applicative (Market a b s)` are removed: a
  `Monocle` without foci made an improper `Prism` breaking even
  @preview l (review l b) = Just b@.

- `Filtroid`, `unlefted` & `unrighted` are removed: by `Filtrator`'s laws,
  its `Cochoice` derives from `Profunctor` & `Filterable`, so an optic for
  `Filtrator`s may only map its source & filter its target, as a
  `filterPrism` does. Use `filterPrism _Left` & `filterPrism _Right`.
- `coPrism` is renamed `filterPrism`, a filter pattern of a `Prism`,
  since the coprism, the action of a reversed `Prism`, is `?<`.

- `PartialIso` drops its `Cochoice` constraint, failing by `Filterable`
  alone, so `preview`, `^?`, `has` & `toListOf` terminate on a
  `PartialIso` which fails to match, rather than looping in `Cochoice (->)`.
  `partialIso` is the action `dimapMaybe` on @p a (f b)@.
  Its action `>?<` on `Choice` & `Cochoice` profunctors is unchanged.
- `Filtrator`'s laws are that `filtrate` is a retraction of `alternate`,
  rather than an inverse of `>+<`, which fails for left-biased &
  predictive parsers, & for profunctors which cross summands.
- `Filtrator (Star f)` is removed, since `Star`'s `Cochoice` retries
  the other summand where `filtrate` drops it, breaking
  `unright = snd . filtrate`.
- `KleeneStarAlgebra (Ap f k)` is removed, since a left-biased `f`,
  like `Maybe`, breaks `optK x = mempty >|< x = x >|< mempty`.
- `Enumerable`, its functions & `Indexing`, renamed `Enumerator`, move from
  `Data.Traversable.Homogeneous` to `Data.Traversable.Homogeneous.Enumerable`.
- `Comonocle`s & their combinators move from `Control.Lens.Monocle` to
  their own module, `Control.Lens.Comonocle`.
- `Data.Profunctor.Separator` merges into `Control.Lens.Prismoid`:
  `Operator`, `Assoc` & `withOperators`.
- `manied`, `chained1` & `chained` are renamed `several`, `chain1` &
  `chain`, & `somed` is `atLeast 1`, replacing the `SepBy` combinators
  `several`, `chain1` & `chain`, which `sepBy` of them replaces:
  `several sep p` is `sepBy sep several p`, of lists, &
  `listed ~< sepBy sep several p` of other `IsList`s;
  `several1 sep p` is `sepBy sep (atLeast 1) p`;
  `chain1 assoc pat sep p` is `sepBy sep (chain1 assoc pat) p`; &
  `intercalateP n sep p` is `sepBy sep (exactly n) p`.
- `SepBy` & `noSep` are removed, & `sepBy` is now the action of a
  `Prismoid` with a separator, rather than a `SepBy` smart constructor:
  delimiters compose around it, `beg >* sepBy sep pat p *< end`; with
  no separator, `sepBy oneP pat = (pat >?*)`.
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
- `Data.Profunctor.Monadic` splits: its qualified do-notation, `>>=`,
  `>>`, `return` & `fail`, moves to `Data.Profunctor.Monadic.Do`, to import
  qualified, leaving `Monadic` to import unqualified, with no names
  conflicting with the `Prelude`.
- `MonadicTry` moves from `Data.Profunctor.Monadic` to
  `Control.Monad.Fail.Try`, which `Data.Profunctor.Monadic` no longer
  imports, & `Data.Profunctor.Monadic` no longer re-exports `try`.
- `sepWith` moves to `Control.Lens.Grammar.Symbol` & takes a `Prismoid`,
  `sepWith str = sepBy (terminal str)`, so `several1 (sepWith ",") p` is
  `sepWith "," (atLeast 1) p`; `beginWith` & `endWith` are removed, as
  delimiters compose around it by `>*` & `*<`.

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

