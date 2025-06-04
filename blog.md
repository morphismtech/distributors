# Unifying Parsers, Printers, and Grammars: A Profunctorial & Optics-Based Perspective

## 0. Introduction

In the world of functional programming, the quest for composable, invertible, and declarative syntax descriptions has led to a convergence of ideas from category theory, optics, and parser combinator libraries. This post explores a modern approach to invertible syntax—one that leverages profunctors, optics, and monoidal structures to unify parsing, pretty-printing, and grammar specification. The approach is inspired by the "Invertible Syntax Descriptions" paper by Rendel & Ostermann, but is recast in the language of profunctors and optics, as realized in the [distributors](https://github.com/morphismtech/distributors) library.

## 1. Previous Work

The foundation for invertible syntax comes from Rendel & Ostermann's [Invertible Syntax Descriptions](https://www.mathematik.uni-marburg.de/~rendel/rendel10invertible.pdf), which introduced the idea of using partial isomorphisms to describe syntax that can be both parsed and pretty-printed. This work has influenced a wide range of libraries and languages, from Haskell's [product-profunctors](https://github.com/tomjaguarpaw/product-profunctors) and [one-liner](https://github.com/sjoerdvisscher/one-liner) to Swift's [swift-parsing](https://github.com/pointfreeco/swift-parsing).

The lens library by Ed Kmett brought the power of optics to programming, enabling composable data access and transformation. More recently, the study of monoidal profunctors, grates, monocles, and withers has deepened our understanding of composable, bidirectional transformations.

## 2. Printor and Parsor Profunctors

At the heart of this approach are two profunctors: `Printor` and `Parsor`. A profunctor is a generalization of a functor that is contravariant in its first argument and covariant in its second. In the context of syntax, a `Parsor` is a profunctor that consumes input and produces a value (parsing), while a `Printor` is a profunctor that consumes a value and produces output (printing).

By treating both parsers and printers as profunctors, we can define combinators and abstractions that work uniformly in both directions. This symmetry is the key to invertible syntax.

## 3. Partial Isomorphisms

Partial isomorphisms are the building blocks of invertible syntax. A partial isomorphism is a pair of partial functions that are inverses of each other on their domains. In Haskell, this is captured by the `PartialIso` type, which provides combinators for sequencing, alternation, and mapping.

Partial isomorphisms allow us to describe the relationship between a concrete syntax (e.g., a string) and an abstract value (e.g., an AST node) in a way that is invertible—every parse can be pretty-printed, and vice versa.

## 4. Monoidal Profunctors

To build complex syntax descriptions from simpler ones, we need a way to compose profunctors. This is where monoidal profunctors come in. A monoidal profunctor is a profunctor equipped with operations for combining and splitting inputs and outputs, analogous to the `Applicative` interface for functors.

Monoidal profunctors enable the definition of combinators for sequencing, optionality, and repetition, all in a way that preserves invertibility.

## 5. Distributors & Homogeneous Functors

The term "distributor" is used here as a synonym for profunctor, following the terminology of Jean Bénabou. In this library, a `Distributor` is a profunctor on a distributive category, and it generalizes the notion of a functor in the same way that a distribution generalizes a function.

Homogeneous functors are functors that act uniformly on their arguments. In the context of syntax, they allow us to define generic combinators that work for both parsing and printing, further unifying the two directions.

## 6. Alternator & Filtrators

Just as `Applicative` functors have `Alternative` for choice and failure, monoidal profunctors have `Alternator` and `Filtrator`. An `Alternator` provides combinators for alternation (choice) in syntax, while a `Filtrator` provides combinators for filtering (guarding) values.

These abstractions allow us to express complex, context-sensitive grammars in a composable and invertible way.

## 7. Tokenized

The `Tokenized` abstraction captures the idea of working with streams of tokens, rather than raw characters or bytes. By defining profunctorial combinators that operate on token streams, we can build syntax descriptions that are independent of the underlying representation, making them more reusable and composable.

## 8. Regular Expressions

Regular expressions are a classic example of compositional syntax. In this framework, regular expressions are described using monoidal profunctors and partial isomorphisms, allowing them to be both parsed and pretty-printed. The library provides a `RegEx` type and combinators for sequencing, alternation, repetition, and character classes, all in an invertible way.

## 9. Grammars

Finally, grammars are described as values of the `Grammar` type, which is a higher-order abstraction over profunctors. A `Grammar` can be interpreted as a parser, a printer, or a regular expression, depending on the profunctor instance used.

By unifying grammars, parsers, and printers under the profunctorial and optics-based approach, we gain a powerful and expressive framework for language design, transformation, and analysis.

---

This approach not only realizes the vision of invertible syntax descriptions but also extends it with the full power of optics, profunctors, and category theory, providing a modern foundation for composable, bidirectional syntax in functional programming.
