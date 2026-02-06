# Changelog for `distributors`

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

