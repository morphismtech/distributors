# Distributors
**Unifying Parsers, Printers & Grammars**
**Eitan Chatav**
## Parsers & Printers
The Haskell programming language is well known to provide a rich environment in which to study parsing. It is in this setting that a major advance in understanding was explained by Conor McBride & Ross Paterson in [Applicative Programming with Effects](https://www.staff.city.ac.uk/~ross/papers/Applicative.html). This paper introduced the `Applicative` interface in programming, idiom brackets, and the `Traversable` interface. The final section gives a category theoretical perspective, identifying `Applicative` with lax monoidal functors. These ideas set off a bonanza of work, including on the closely related `Alternative` interface and "parser combinators".

Next, Tillmann Rendel & Klaus Ostermann, noticing that parsing & printing are inverse to one another set out to unify their interfaces in [Invertible Syntax Descriptions](https://www.informatik.uni-marburg.de/~rendel/unparse/). When designing a language syntax, programmers usually have to write both a parser _and_ a printer, violating the [Don't Repeat Yourself](https://en.wikipedia.org/wiki/Don%27t_repeat_yourself) principle. The paper reasons that if a syntax is described using parser combinators, then one should be able to use the same combinators to generate both parsers _and_ printers. But unifying the interfaces runs into an immediate issue; while the `Parser` type is a covariant `Functor`, the `Printer` type is instead a `Contravariant` functor.

```
newtype Parser a = Parser (String -> [(a,String)])

instance Functor Parser where
  fmap f (Parser p) = Parser $ \str ->
    [(f a, str') | (a, str') <- p str]

newtype Printer a = Printer (a -> Maybe String)

instance Contravariant Printer where
  contramap f (Printer p) = Printer $ p . f
```

Any covariant `Functor` which is _also_ `Contravariant` is an "invariant", or "phantom", a.k.a. constant functor, which is too strong of a constraint for parsers. So, the paper instead _drops_ the `Functor` constraint from the usual `Applicative` and `Alternative` parser combinators. At the time another natural interface from category theory had not yet found its way to Haskell, [profunctors](https://ncatlab.org/nlab/show/profunctor).

## Profunctors

A profunctor is a bifunctor which is contravariant in its first argument and covariant in its second argument.

```
class Profunctor p where
  dimap :: (s -> a) -> (b -> t) -> p a b -> p s t

  lmap :: (s -> a) -> p a b -> p s b
  lmap g = dimap id g

  rmap :: (b -> t) -> p a b -> p a t
  rmap g = dimap id g
```

The `Profunctor` interface was introduced to Haskell by Ed Kmett who noticed their utility in representing optics, more on which later. The prototypical example of a `Profunctor` is `(->)`.

```
instance Profunctor (->) where
  dimap sa bt ab = bt . ab . sa
```

Let's see how we can unify parsers & printers with a `Profunctor` interface.

```
newtype Parsor s f a b = Parsor {runParsor :: s -> f (b,s)}

instance Functor f => Profunctor (Parsor s f) where
  dimap _ g (Parsor p) = Parsor (fmap (\(c,str) -> (g c, str)) . p)

newtype Printor s f a b = Printor {runPrintor :: a -> f (s -> s)}

instance Profunctor (Printor s f) where
  dimap f _ (Printor p) = Printor (p . f)
```

Besides changing a vowel in the names, we added a few generalizations to the parser & printer types. First, both types get a phantom type parameter, the `a` in `Parsor` and the `b` in `Printor`. Next, `String` has been polymorphized to `s`. After all, we might want to parse & print `Text` or `ByteString`s or any streams of some lexical token type. Next, the printer type's "result" is upgraded to an endofunction `s -> s`. This makes it a more fully dualized definition to the parser type, and is a common trick used in printer types such as `ShowS`. Finally, the "container" for the result of a parse or print has been polymorphized to `f`. Usually this will be `[]` or `Maybe` but we should take a moment to address a subtle point here.

Printing is usually conceived an exhaustive affair; one defines a single function `X -> String` by pattern matching on each case of an `X`. Parsing however is usually a partial affair; one defines a bunch of partial parsers for each case of the `X` and combines them into one with the `Alternative` combinator `(<|>)`. By polymorphizing `f` in the definitions of the `Printor`, we can address either situation by restricting to only `Applicative f` when we want exhaustivity and allowing `Alternative f` when we want partiality.

## Optics & Patterns

Optics are an ongoing field of advanced study in applied category theory and computer science which makes giving an exact definition challenging. In Haskell, research into "semantic editor combinators" led to noticing the composability of such combinators as record field accessors or data constructor patterns, leading to the discovery of optics. Much can  and has been written about lenses, traversals & prisms that can't be written about here. The most important thing from our perspective will be the relation between profunctors and optics. Moreover the variety of optics that we will be most interested in will represent "patterns".

Let's start with two definitions of _isomorphism_ optics. Isomorphism optics are pairs of functions, one in a "backwards" direction and one in a "forwards" direction, like a `newtype` constructor pattern.

```
data Exchange a b s t = Exchange (s -> a) (b -> t)

type Iso s t a b = forall p f.
  (Profunctor p, Functor f) => p a (f b) -> p s (f t)
```

The `Exchange` type is a "concrete representation" of the isomorphism optic and `Iso` is a "Kmett representation". They're equivalent and you can convert between representations. The [lens library](https://hackage.haskell.org/package/lens) uses Kmett's representation as it provides a convenient specialization to a "Van Laarhoven representation" when `p` is `(->)`. However, a pure profunctorial representation (without `f`), which is also equivalent, can be simpler. We can observe the profunctorial representation with a combinator.

```
mapIso :: Profunctor p => Iso s t a b -> p a b -> p s t
mapIso pattern = withIso pattern dimap
```

Now, let's move on to our next optic example, prisms. `Prism`s encode exhaustive patterns. To encode them we first need the `Choice` interface.

```
class Profunctor p => Choice p where
  left' :: p a b -> p (Either a c) (Either b c)
  right' :: p a b -> p (Either c a) (Either c b)
```

Now we can define a concrete prism type consisting of a pair of functions, a constructor and destructor for a pattern match, as well as defining the abstract `Prism` type.

```
data Market a b s t = Market (b -> t) (s -> Either t a)

type Prism s t a b = forall p f.
  (Choice p, Applicative f) => p a (f b) -> p s (f t)

type Prism' s a = Prism s s a a
```

The `Applicative f` in the definition of `Prism` makes it so that every `Prism` is automatically a `Traversal`. But again, for our purpose we're most interested in the pure profunctor representation which we can observe with a new combinator.

```
(>?) :: Choice p => Prism s t a b -> p a b -> p s t
(>?) pattern = withPrism pattern $ \f g -> dimap g (either id f) . right'
```

It turns out that both `Parsor` and `Printor` have `Choice` instances so that `(>?)` becomes both a parser combinator _and_ a printer combinator. The lens library provides Template Haskell functions to make `Prism`s from the pattern constructors of algebraic datatypes. Or we can construct `Prism`s like `only` from a pair of functions using the `prism'` or `prism` smart constructors.

```
only :: Eq a => a -> Prism' a ()
only a = prism' (\() -> a) $ guard . (a ==)
```

Next, we may consider the dual to prisms, coprisms. If `Prism`s encode pattern matching, then coprisms encode pattern filtering. To encode them we first need the `Cochoice` interface, which we get from `Choice` by reversing arrows.

```
class Profunctor p => Cochoice p where
  unleft :: p (Either a c) (Either b c) -> p a b
  unright :: p (Either c a) (Either c b) -> p a b
```

Actually, we don't really need to encode coprisms. Since they are dual to prisms we can just shuffle the indices of the `Prism` type to encode coprisms and observe the pure profunctor representation with our next combinator.

```
(?<) :: Cochoice p => Prism b a t s -> p a b -> p s t
(?<) pattern = withPrism pattern $ \f g -> unright . dimap (either id f) g
```

Both `Parsor` and `Printor` have `Cochoice` instances too. We will call a profunctor with both `Choice` & `Cochoice` instances a "partial profunctor". Partial profunctors support a combinator `dimapMaybe`.

```
dimapMaybe
  :: (Choice p, Cochoice p)
  => (s -> Maybe a) -> (b -> Maybe t)
  -> p a b -> p s t
dimapMaybe f g =
  let
    m2e h = maybe (Left ()) Right . h
    fg = dimap (>>= m2e f) (>>= m2e g)
  in
    unright . fg . right'
```

We can turn the pair of partial functions into another optic, partial isomorphisms.

```
data PartialExchange a b s t = PartialExchange (s -> Maybe a) (b -> Maybe t)

type PartialIso s t a b = forall p f.
  ( Choice p, Cochoice p
  , Applicative f, Filterable f
  ) => p a (f b) -> p s (f t)

type PartialIso' s a = PartialIso s s a a
```

You may not have seen the `Filterable` interface before. It is a very simple interface from the [witherable library](https://hackage.haskell.org/package/witherable) that generalizes the list functions `catMaybes`, `filter` and `mapMaybe`.

```
class Functor f => Filterable f where
  mapMaybe :: (a -> Maybe b) -> f a -> f b
  mapMaybe f = catMaybes . fmap f

  catMaybes :: f (Maybe a) -> f a
  catMaybes = mapMaybe id

  filter :: (a -> Bool) -> f a -> f a
  filter f = mapMaybe $ \a -> if f a then Just a else Nothing
```

`Filterable` is dual to the `Alternative` interface, which can be seen by comparing the signature of `catMaybes` to `optional`.

```
optional :: Alternative f => f a -> f (Maybe a)
```

We can now turn `dimapMaybe` into a combinator on `PartialIso`s.

```
(>?<) :: (Choice p, Cochoice p) => PartialIso s t a b -> p a b -> p s t
```

The prototypical example of a `PartialIso` is a subset which has `satisfied` a predicate which we can construct from a pair of functions with the smart constructor `partialIso`.

```
satisfied :: (a -> Bool) -> PartialIso' a a
satisfied f = partialIso satiate satiate where
  satiate a = if f a then Just a else Nothing
```

## Tokens

Combinators are great for generating new printer-parsers from existing ones, but if we want to generate examples we need an interface which generates basic printer-parsers from scratch. For that purpose, we define the `Tokenized` interface.

```
class Tokenized a b p | p -> a, p -> b where
  anyToken :: p a b

data Identical a b s t where
  Identical :: Identical a b a b
instance Tokenized a b (Identical a b) where
  anyToken = Identical
```

The `Tokenized` interface is so abstract it would lack any obvious motivation if not for its name. We want `anyToken` to sequence any single token from the head of the printer-parser stream type `s`. Recall that `s` appears as both input and output in the definitions of `Parsor` & `Printor`. If `s` were `String` then `anyToken` would correspond to the "cons" pattern `(:)` which conses (prints) or unconses (parses) any single `Char` to or from the head of the `String`. The lens library provides a `Cons` interface which generalizes the `(:)` pattern, letting us remain polymorphic over the stream type.

```
class Cons s t a b | s -> a, t -> b, s b -> t, t a -> s where
  _Cons :: Prism s t (a,s) (b,t)

instance (Applicative f, Cons s s c c)
  => Tokenized c c (Printor s f) where
    anyToken = Printor (pure . cons)

instance (Alternative f, Cons s s c c)
  => Tokenized c c (Parsor s f) where
    anyToken = Parsor (maybe empty pure . uncons)
```

Now we can see our first printer-parser in action.

```
>>> runParsor anyToken "xyz" :: [(Char,String)]
[('x',"yz")]
>>> runParsor anyToken "" :: [(Char,String)]
[]
>>> [pr "yz" | pr <- runPrintor anyToken 'x'] :: [String]
["xyz"]
```

We can also form a couple new combinators.

```
token :: (Cochoice p, Eq c, Tokenized c c p) => c -> p () ()
token c = only c ?< anyToken

satisfy :: (Choice p, Cochoice p, Tokenized c c p) => (c -> Bool) -> p c c
satisfy f = satisfied f >?< anyToken

>>> runParsor (token 'x') "xyz" :: [(Char,String)]
[('x',"yz")]
>>> runParsor (satisfy isLower) "xyz" :: [(Char,String)]
[('x',"yz")]
>>> runParsor (satisfy isLower) "X" :: [(Char,String)]
[]
>>> [pr "" | pr <- runPrintor (satisfy isLower) 'X'] :: [String]
[]
```

## Monoidal Profunctors

Before profunctors found their way into Haskell, another interface `Arrow`s were introduced. In [Generalizing Monads to Arrows](https://www.cse.chalmers.se/~rjmh/Papers/arrows.pdf), John Hughes introduces the interface inspired by the example of parsers. In the [Applicative Programming with Effects](https://www.staff.city.ac.uk/~ross/papers/Applicative.html) paper mentioned earlier they note about `Arrow`s:

> By fixing the first argument of an arrow type, we obtain an applicative functor.
..
> Indeed one of Hughes’s motivations was the parsers of Swierstra and Duponcheel (1996). It may turn out that applicative functors are more convenient for applications of the second class

So `Arrow`s are already `Applicative` but they're _also_ already (`Strong`) `Profunctor`s, bearing the same relation to them as `Monad` bears to `Functor`. We want to find the missing spot in this table.

|(Type -> Type) -> Constraint|(Type -> Type -> Type) -> Constraint|
|-|-|
|Functor|Profunctor|
|Applicative|???|
|Monad|Arrow

This interface has variously been called a product profunctor or a (lax) monoidal profunctor. It turns out it's equivalent to a constraint synonym, hinted at in the quote.

```
type Monoidal p = (Profunctor p, forall x. Applicative (p x))
```

It's not new at all, just the combination of the two interfaces, enabled by the quantified constraints extension. Both `Parsor` and `Printor` support this interface since they have `Applicative` instances.

```
instance Monad f => Applicative (Parsor s f a) where
  pure b = Parsor (\str -> return (b,str))
  Parsor x <*> Parsor y = Parsor $ \str -> do
    (f, str') <- x str
    (a, str'') <- y str'
    return (f a, str'')

instance Applicative f => Applicative (Printor s f a) where
  pure _ = Printor (\_ -> pure id)
  Printor p <*> Printor q = Printor (\a -> (.) <$> p a <*> q a)
```

We can now define sequencing combinators for `Monoidal` profunctors.

```
oneP :: Monoidal p => p () ()
oneP = pure ()

(>*<) :: Monoidal p => p a b -> p c d -> p (a,c) (b,d)
x >*< y = (,) <$> lmap fst x <*> lmap snd y

(>*) :: Monoidal p => p () c -> p a b -> p a b
x >* y = lmap (const ()) x *> y

(*<) :: Monoidal p => p a b -> p () c -> p a b
x *< y = x <* lmap (const ()) y
```

In `Applicative` parsing one uses an "idiom style"  with the functor mapping combinator `<$>` and sequencing combinators `<*>`, `*>` & `<*`. In `Monoidal` parsing one can use the same idiom style, with partial profunctor mapping combinator `>?<` together with sequencing combinators `>*<`, `>*` & `*<`.

We can also form the `tokens` combinator, which we can use to give `IsString` instances to `Parsor` and `Printor`.

```
tokens :: (Cochoice p, Monoidal p, Eq c, Tokenized c c p) => [c] -> p () ()
tokens [] = oneP
tokens (c:cs) = token c *> tokens cs

instance (Alternative f, Filterable f, Monad f, Cons s s Char Char)
  => IsString (Parsor s f () ()) where
    fromString = tokens

instance (Applicative f, Cons s s Char Char)
  => IsString (Printor s f () ()) where
    fromString = tokens

>>> :set -XOverloadedStrings
>>> runParsor "abc" "abcxyz" :: [((),String)]
[((),"xyz")]
>>> [pr "xyz" | pr <- runPrintor "abc" ()] :: [String]
["abcxyz"]
```

More combinators can be added and monoidal profunctors have been well studied, including their corresponding optics called monocles, which are related to traversal & grate optics.

## Distributors

The `Applicative` interface is the star of the show when it comes to parsing, while the `Alternative` interface by comparison gets too little attention. Let's revisit it.

```
class Applicative f => Alternative f where
  empty :: f a
  (<|>) :: f a -> f a -> f a
```

We can re-characterize `Alternative` with methods `zeroF` & `(<+>)` instead of `empty` & `(<|>)`, in order to see more clearly how the `Alternative` interface relates to the nilary and binary coproducts `Void` and `Either`.

```
zeroF :: Alternative f => f Void
zeroF = empty

(<+>) :: Alternative f => f a -> f b -> f (Either a b)
a <+> b = Left <$> a <|> Right <$> b

prop> empty = absurd <$> zeroF
prop> a <|> b = either id id <$> (a <+> b)
```

Unfortunately, the same trick used to define `Monoidal` as a combination of `Profunctor` and `Applicative` does not work for the `Alternative` interface. So we introduce the `Distributor` interface, which analogizes the above re-characterization of `Alternative` to profunctors.

```
class Monoidal p => Distributor p where
  zeroP :: p Void Void
  (>+<) :: p a b -> p c d -> p (Either a c) (Either b d)
```

Just as `Alternative` has 0-or-more `many` and 0-or-1 `optional` combinators, we can define `manyP` and `optionalP`.

```
optionalP :: Distributor p => p a b -> p (Maybe a) (Maybe b)
optionalP p = mapIso maybeEot (oneP >+< p)

manyP :: p a b -> p [a] [b]
manyP p = mapIso listEot (oneP >+< p >*< manyP p)

maybeEot :: Iso (Maybe a) (Maybe b) (Either () a) (Either () b)

listEot
  :: (Cons s s a a, AsEmpty t, Cons t t b b)
  => Iso s t (Either () (a,s)) (Either () (b,t))
```

The prototypical example of a `Distributor` is `(->)`. Unlike monoidal profunctors, distributors have not been very well studied. Like `Alternative` this interface doesn't seem to get the attention it deserves. The name was coined by Jean Bénabou who invented the term and originally used “profunctor,” then preferred “[distributor](http://www.entretemps.asso.fr/maths/Distributors.pdf)”. Since "profunctor" became the preferred nomenclature, we use "distributor" or lax distributive profunctor for this more restrictive interface since it uses the distributive structure on the category with `()`, `(,)`, `Void` & `Either`. Its corresponding optics which I dubbed "diopters" can be thought of as positional patterns. If you transform an algebraic datatype into its "eithers-of-tuples" representation, you can match its algebraic structure with the algebraic combinators `>*<`, `oneP`, `>+<` & `zeroP`.

`Distributor`s are like an _exhaustive_ analog to `Alternative` for profunctors, but if we want to have partiality and failure we need this next interface with an even stronger analogy to `Alternative`.

```
class (Choice p, Distributor p, forall x. Alternative (p x)) => Alternator p where
  alternate :: Either (p a b) (p c d) -> p (Either a c) (Either b d)
```

The `Alternator` interface extends `Choice`, `Distributor` & `Alternative` with a method `alternate` that lets us default the `Distributor` methods.

```
prop> zeroP = empty
prop> x >+< y = alternate (Left x) <|> alternate (Right y)
```

In the functorial case, the two descriptions of `Alternative` in terms of either `zeroF` & `<+>` or `empty` & `<|>` are equivalent but in the profunctorial case, they're distinguished into the `Distributor` interface which can be exhaustive and the `Alternator` interface which must be partial. Since `(->)` is not `Alternative`, it is an example of a `Choice` `Distributor` which is not an `Alternator`. However, `Parsor` and `Printor` have instances.

```
instance (Alternative f, Monad f) => Alternative (Parsor s f a) where
  empty = Parsor (\_ -> empty)
  Parsor p <|> Parsor q = Parsor (\str -> p str <|> q str)

instance (Alternative f, Monad f) => Alternator (Parsor s f) where
  alternate = \case
    Left (Parsor p) -> Parsor (fmap (\(b, str) -> (Left b, str)) . p)
    Right (Parsor p) -> Parsor (fmap (\(b, str) -> (Right b, str)) . p)

instance (Alternative f, Monad f) => Distributor (Parsor s f)

instance Alternative f => Alternative (Printor s f a) where
  empty = Printor (\_ -> empty)
  Printor p <|> Printor q = Printor (\a -> p a <|> q a)

instance Applicative f => Distributor (Printor s f) where
  zeroP = Printor absurd
  Printor p >+< Printor q = Printor (either p q)

instance Alternative f => Alternator (Printor s f) where
  alternate = \case
    Left (Printor p) -> Printor (either p (\_ -> empty))
    Right (Printor p) -> Printor (either (\_ -> empty) p)
```

`Parsor`s are `Distributor`s exactly when they are `Alternator`s, using default methods for `zeroP` and `>+<`. Notice however that `Printor`'s `Distributor` instance works for exhaustive printers while its `Alternator` instance only works for partial printers. With `Alternator`, we can extend `Alternative`s partial 1-or-more combinator `some` profunctorially.

```
someP :: Alternator p => p a b -> p [a] [b]
someP p = _Cons >? p >*< manyP p
```

Recall that the `Filterable` interface was dual to the `Alternative` interface. We can extend `Filterable` profunctorially, dualizing the `Distributor` interface. A "partial distributor" means both `Alternator` & `Filtrator`.

```
class (Cochoice p, forall x. Filterable (p x)) => Filtrator p where
  filtrate :: p (Either a c) (Either b d) -> (p a b, p c d)

instance Filterable f => Filtrator (Parsor s f) where
  filtrate (Parsor p) =
    ( Parsor (mapMaybe leftMay . p)
    , Parsor (mapMaybe rightMay . p)
    ) where
      leftMay (e, str) = either (\b -> Just (b, str)) (\_ -> Nothing) e
      rightMay (e, str) = either (\_ -> Nothing) (\b -> Just (b, str)) e

instance Filtrator (Printor s f) where
  filtrate (Printor p) = (Printor (p . Left), Printor (p . Right))
```

Now that we've developed all of our basic combinators, let's write a simple printer-parser example for positive decimal integers.

```
>>> :{
posDecInt :: (Tokenized Char Char p, Alternator p) => p Int Int
posDecInt = _Show >?
  someP (satisfy (\c -> generalCategory c == DecimalNumber))
:}
>>> runParsor posDecInt "2001 A Space Odyssey" :: [(Int,String)]
[(2,"001 A Space Odyssey"), (20,"01 A Space Odyssey"), (200,"1 A Space Odyssey"), (2001," A Space Odyssey")]
>>> [pr " A Space Odyssey" | pr <- runPrintor posDecInt 2001] :: [String]
["2001 A Space Odyssey"]
```

Partial distributors have associated optics which I dubbed "bifocals".

## Grammars

In a blog post [Showcasing Applicative](https://www.joachim-breitner.de/blog/710-Showcasing_Applicative) by Joachim Breitner, he demonstrates an example of extended Backus-Naur form grammars as a constant `Applicative` functor. Inspired by this idea and the similar example of regular expressions as `Applicative`s, we can extend partial distributors to `Grammatical` distributors.

```
class
  ( Alternator p, Filtrator p
  , Tokenized Char Char p
  , forall t. t ~ p () () => IsString t
  ) => Grammatical p where

    inClass :: String -> p Char Char
    inClass str = satisfy $ \ch -> elem ch str

    notInClass :: String -> p Char Char
    notInClass str = satisfy $ \ch -> notElem ch str

    inCategory :: GeneralCategory -> p Char Char
    inCategory cat = satisfy $ \ch -> cat == generalCategory ch

    notInCategory :: GeneralCategory -> p Char Char
    notInCategory cat = satisfy $ \ch -> cat /= generalCategory ch

    rule :: String -> p a a -> p a a
    rule _ = id

    ruleRec :: String -> (p a a -> p a a) -> p a a
    ruleRec name = rule name . fix

instance (Alternative f, Cons s s Char Char)
  => Grammatical (Printor s f)
instance (Monad f, Alternative f, Filterable f, Cons s s Char Char)
  => Grammatical (Parsor s f)
```

Notice that all the methods of `Grammatical` have defaults which the `Printor` and `Parsor` instances use. We could overwrite them for other instances. The methods `inClass`, `notInClass`, `inCategory` and `notInCategory` are "regular predicates", i.e. predicates that have special regular expressions associated to them. The methods `rule` and `ruleRec` correspond to "nonterminal rules" in an extended Backus-Naur form grammar. The defaults for these methods completely ignores the rule names and just inlines the rules using `id` for non-recursive and `fix` for recursive rules. So, why have rule names if they're meaningless? A more full-featured parser type than `Parsor` would incorporate useful error messaging. For instance all parsec style parsers have a combinator `<?>` or `label` which can be used to over-write `rule` for a newtyped parsec `Grammatical` instance so that rule names show up when there is a parse failure.

Now, we can define a type `Grammar` which gives us a "final tagless encoding" of Backus-Naur grammars extended by regular expressions and "type-directed" by a Haskell type `a`.

```
type Grammar a = forall p. Grammatical p => p a a

genReadS :: Grammar a -> ReadS a
genReadS = runParsor

genShowS :: Alternative f => Grammar a -> a -> f ShowS
genShowS = runPrintor
```

In a lot of discussions about different options in the space of parsing tools, much is made of contrasting parser combinators and parser generators. However, this is a false dichotomy. Combinators are methods (or functions derived from methods) of type classes. Generators as we can see from `genReadS` and `genShowS` come from instances of those type classes. This makes the final tagless embedding approach extensible. To define a new generator, for instance for a parsec style parser, you just need to define a new type and instances for it up to `Grammatical`.

Even with only very low level combinators, we have almost enough to give a non-trivial example of a `Grammar` for an abstract syntax tree. The syntax we choose for the example is a form of regular expressions. This is an ideal example because it is (hopefully) familiar. It is prototypical as an "arithmetic expression algebra". It is complex enough to stress test `Grammar`s. It's almost the homework problem at the end of the blog post. And it matches up with the embedded language which will let us define _more_ generators.

```
data RegEx
  = Terminal String -- abc123etc\.
  | Sequence RegEx RegEx -- xy
  | Fail -- \q
  | Alternate RegEx RegEx -- x|y
  | KleeneOpt RegEx -- x?
  | KleeneStar RegEx -- x*
  | KleenePlus RegEx -- x+
  | AnyChar -- .
  | InClass String -- [abc]
  | NotInClass String -- [^abc]
  | InCategory GeneralCategory -- \p{Lu}
  | NotInCategory GeneralCategory -- \P{Ll}
  | NonTerminal String -- \q{rule-name}
  deriving stock (Eq, Ord, Show, Generic)
```

Before we are able however to write our grammar, we will need a couple slightly higher level combinators. A very common feature of syntax is lists which are recognized using beginning, ending and separator delimiters.

```
data SepBy p = SepBy
  { beginBy :: p () ()
  , endBy :: p () ()
  , separateBy :: p () ()
  }

sepBy :: Monoidal p => p () () -> SepBy p
sepBy = SepBy oneP oneP

noSep :: Monoidal p => SepBy p
noSep = sepBy oneP

chainl1
  :: (Choice p, Cochoice p, Distributor p)
  => APartialIso a b (a,a) (b,b) -- ^ binary constructor pattern
  -> SepBy p -> p a b -> p a b

chainl
  :: (Alternator p, Filtrator p)
  => APartialIso a b (a,a) (b,b) -- ^ binary constructor pattern
  -> APartialIso a b () () -- ^ nilary constructor pattern
  -> SepBy p -> p a b -> p a b
```

Assuming these combinators have definitions, we are now in a position to define our regular expression `Grammar`.

```
regexGrammar :: Grammar RegEx
regexGrammar = ruleRec "regex" altG

makePrisms ''RegEx

altG rex = rule "alternate" $
  chainl1 _Alternate (sepBy "|") (seqG rex)

anyG = rule "any" $ _AnyChar >?< "."

atomG rex = rule "atom" $
  nonterminalG
  <|> failG
  <|> classInG
  <|> classNotInG
  <|> categoryInG
  <|> categoryNotInG
  <|> _Terminal . _Cons >?< charG >*< pure ""
  <|> anyG
  <|> parenG rex

makePrisms ''GeneralCategory

categoryG = rule "category" $
  _LowercaseLetter >?< "Ll"
  <|> _UppercaseLetter >?< "Lu"
  <|> _TitlecaseLetter >?< "Lt"
  <|> _ModifierLetter >?< "Lm"
  <|> _OtherLetter >?< "Lo"
  <|> _NonSpacingMark >?< "Mn"
  <|> _SpacingCombiningMark >?< "Mc"
  <|> _EnclosingMark >?< "Me"
  <|> _DecimalNumber >?< "Nd"
  <|> _LetterNumber >?< "Nl"
  <|> _OtherNumber >?< "No"
  <|> _ConnectorPunctuation >?< "Pc"
  <|> _DashPunctuation >?< "Pd"
  <|> _OpenPunctuation >?< "Ps"
  <|> _ClosePunctuation >?< "Pe"
  <|> _InitialQuote >?< "Pi"
  <|> _FinalQuote >?< "Pf"
  <|> _OtherPunctuation >?< "Po"
  <|> _MathSymbol >?< "Sm"
  <|> _CurrencySymbol >?< "Sc"
  <|> _ModifierSymbol >?< "Sk"
  <|> _OtherSymbol >?< "So"
  <|> _Space >?< "Zs"
  <|> _LineSeparator >?< "Zl"
  <|> _ParagraphSeparator >?< "Zp"
  <|> _Control >?< "Cc"
  <|> _Format >?< "Cf"
  <|> _Surrogate >?< "Cs"
  <|> _PrivateUse >?< "Co"
  <|> _NotAssigned >?< "Cn"

categoryInG = rule "category-in" $
  _InCategory >?< "\\p{" >* categoryG *< "}"

categoryNotInG = rule "category-not-in" $
  _NotInCategory >?< "\\P{" >* categoryG *< "}"

charG = rule "char" $ charLiteralG <|> charEscapedG

charEscapedG = rule "char-escaped" $ "\\" >* inClass charsReserved

charLiteralG = rule "char-literal" $ notInClass charsReserved

charsReserved = "$()*+.?[\\]^{|}"

classInG = rule "class-in" $
  _InClass >?< "[" >* manyP charG *< "]"

classNotInG = rule "class-not-in" $
  _NotInClass >?< "[^" >* manyP charG *< "]"

exprG rex = rule "expression" $
  terminalG
  <|> kleeneOptG rex
  <|> kleeneStarG rex
  <|> kleenePlusG rex
  <|> atomG rex

failG = rule "fail" $ _Fail >?< "\\q"

nonterminalG = rule "nonterminal" $
  _NonTerminal >?< "\\q{" >* manyP charG *< "}"

parenG ex = rule "parenthesized" $ "(" >* ex *< ")"

kleeneOptG rex = rule "kleene-optional" $
  _KleeneOpt >?< atomG rex *< "?"

kleeneStarG rex = rule "kleene-star" $
  _KleeneStar >?< atomG rex *< "*"

kleenePlusG rex = rule "kleene-plus" $
  _KleenePlus >?< atomG rex *< "+"

seqG rex = rule "sequence" $
  chainl _Sequence (_Terminal . _Empty) noSep (exprG rex)

terminalG = rule "terminal" $ _Terminal >?< someP charG
```

It's not as beautiful as it could be but it works and its rough edges can be smoothed. Now, the `RegExp` type morally has the same "shape" as the `Grammatical` interface. So, to create a new generators we define a couple invariant profunctors inspired by the blog post, and I leave their instances as exercises.

```
newtype DiRegEx a b = DiRegEx RegEx

data DiGrammar a b = DiGrammar
  { grammarStart :: DiRegEx a b
  , grammarRules :: Set (String, RegEx)
  }

genRegEx :: Grammar a -> RegEx
genRegEx (DiRegEx rex) = rex

genGrammar :: Grammar a -> [(String, RegEx)]
genGrammar (DiGrammar (DiRegEx start) rules) =
  ("start", start) : toList rules
```

Putting together the regular expression grammar `regexGrammar` with the grammar generator `genGrammar` and the printer generator `genShowS`, we can even print  a self-contained Backus-Naur form grammar extended by regular expressions (regexBNF) -- of regular expressions.

```
>>> printGrammar regexGrammar
start = \q{regex}
alternate = \q{sequence}(\|\q{sequence})*
any = \.
atom = \q{nonterminal}|\q{fail}|\q{class-in}|\q{class-not-in}|\q{category-in}|\q{category-not-in}|\q{char}|\q{any}|\q{parenthesized}
category = Ll|Lu|Lt|Lm|Lo|Mn|Mc|Me|Nd|Nl|No|Pc|Pd|Ps|Pe|Pi|Pf|Po|Sm|Sc|Sk|So|Zs|Zl|Zp|Cc|Cf|Cs|Co|Cn
category-in = \\p\{\q{category}\}
category-not-in = \\P\{\q{category}\}
char = \q{char-literal}|\q{char-escaped}
char-escaped = \\[\$\(\)\*\+\.\?\[\\\]\^\{\|\}]
char-literal = [^\$\(\)\*\+\.\?\[\\\]\^\{\|\}]
class-in = \[\q{char}*\]
class-not-in = \[\^\q{char}*\]
expression = \q{terminal}|\q{kleene-optional}|\q{kleene-star}|\q{kleene-plus}|\q{atom}
fail = \\q
kleene-optional = \q{atom}\?
kleene-plus = \q{atom}\+
kleene-star = \q{atom}\*
nonterminal = \\q\{\q{char}*\}
parenthesized = \(\q{regex}\)/?
regex = \q{alternate}
sequence = \q{expression}*
terminal = \q{char}+
```

## Extroduction
This post is _not_ literate Haskell. Instead of trying to compile the post, play with this code on [GitHub](https://github.com/morphismtech/distributors/) where it is hopefully kept compiling & tested. This project is a result of a years long obsession. While I am pleased that my obsession has been slaked, there are still more ways these ideas could be extended. `Applicative` & `Alternative` interfaces are useful for more than just parsers. What else are `Monoidal`, `Distributor`, `Alternator` & `Filtrator` useful for? Obviously we need much more than _one_ non-trivial example of a `Grammar`. Want to make and push some more examples? Want to optimize or clean up or document the code some how? Can you construct a useful free `Grammatical` distributor, starting with a base of `Identical Char Char`? Can you use that free `Grammatical` distributor to define a function to left factor and do other useful transformations of grammars? What extensions of distributors can you do besides character stream grammars, like JSON grammars with aeson and typescript type generators? Want to investigate how grammars fit into the pattern optic hierarchy? Want to add some useful higher level grammar combinators? Want to factor exhaustive grammars or regular grammars out from grammar interfaces? Can `Grammar`s generate parsers which aren't recursive descent like an Earley parser, by over-writing `ruleRec`  perhaps?
