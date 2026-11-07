# distributors-json

A `Json` grammar of a type parses, prints & encodes its JSON,
compatibly with `aeson`, & types it in TypeScript, all at once.

```haskell
data Person = Person {name :: Text, age :: Int, email :: Maybe Text}
  deriving stock (Show, Generic)
  deriving anyclass Json
  deriving (ToJSON, FromJSON) via ViaJson Person
```

```haskell
>>> jsonDecode @Person "{\"name\":\"Ada\",\"age\":36}"
Right (Person {name = "Ada", age = 36, email = Nothing})
>>> jsonTsPut (type '[Person]) stdout
export type Int = number;
export type Person = { name: string; age: Int; email?: null | string };
```

See `Control.Lens.Grammar.Json` for a tour, & `Control.Lens.Grammar.TypeScript`
for the TypeScript grammar.
