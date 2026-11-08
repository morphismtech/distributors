# Changelog for distributors-json

## 0.1.0.0

- Split out of `distributors` as its own package.
- `jsonType` types a type's JSON as a `Bnf` of `JsonType`s,
  `jsonTsDeclarations` declares them in TypeScript, & `jsonTsPut` puts
  those declarations to a handle, replacing `jsonTypes`.
- `Control.Lens.Grammar.TypeScript` parses & prints TypeScript type
  declarations, by `tsTokenGrammar` & `tsGrammar`, after the TypeScript
  compiler's scanner & syntax.
- `tsTokensGrammar` scans tokens without their trivia, so that `tsGrammar`
  parses by Parsector, locating failures.
- Mapped types exclude named keys by `as`, rather than the global `Exclude`.
- Single-key objects, like `Either`'s, & numeric keys parse as `aeson` does.
- `jsonObjectStrict` is a `JsonVal` method.
- `jsonPair` is a `JsonVal` method, of pairs & of generic constructors of
  two positional fields, which printing renders as arrays of two elements
  directly.
- `ViaJson` derives all of `aeson`'s instances: `ToJSON` & `FromJSON` with
  `omitField` & `omittedField`, by `jsonOmitField`, & `ToJSONKey` &
  `FromJSONKey`, by `jsonKey` & `jsonKeyList`, or else as values in arrays
  of pairs; & it's `Eq`, `Ord` & `Show`.
- `jsonEnumWith` takes a table of strings & values, & each value's index in it,
  so that it prints by index; generic enumerations index by `dataToTag#`.
