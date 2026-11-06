# distributors

Unifying parsers, printers & grammars, in two packages:

- [`distributors-core`](distributors-core): the `distributors` package,
  of profunctor grammars, which parse, print & generate together.
- [`distributors-json`](distributors-json): the `distributors-json`
  package, of JSON grammars, compatible with `aeson` & typed in TypeScript.

## Building

With Stack:

```sh
stack build --test --bench
DISTRIBUTORS_RUN_DOCTESTS=1 stack test
```

With Cabal:

```sh
cabal build all
cabal test all
```

With Nix:

```sh
nix build .#distributors-json
nix flake check
nix develop # a shell with GHC, Cabal, HLint & hpack
```

Each package's `.cabal` file is generated from its `package.yaml`,
by `hpack`, which Stack runs.
