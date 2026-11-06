# Changelog for distributors-json

## 0.1.0.0

- Split out of `distributors` as its own package.
- `jsonType` types a type's JSON as a `Bnf` of `JsonType`s,
  & `jsonTsDeclarations` declares them in TypeScript, replacing `jsonTypes`.
- `Control.Lens.Grammar.TypeScript` parses & prints TypeScript type
  declarations, by `tsTokenGrammar` & `tsGrammar`, after the TypeScript
  compiler's scanner & syntax.
- Mapped types exclude named keys by `as`, rather than the global `Exclude`.
- Single-key objects, like `Either`'s, & numeric keys parse as `aeson` does.
- `jsonObjectStrict` is a `JsonVal` method.
