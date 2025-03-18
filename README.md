# Distributors
## Unifying Parsers, Printers & Grammars

[![GithubWorkflowCI](https://github.com/morphismtech/squeal/actions/workflows/ci.yml/badge.svg)](https://github.com/morphismtech/squeal/actions/workflows/ci.yml)


This library provides mathematically inspired abstractions for coders to write parsers that can also be inverted to printers.

## introduction
The term "distributor" is a synonym for "[profunctor](https://ncatlab.org/nlab/show/profunctor)". Jean Bénabou who invented the term and originally used “profunctor,” then preferred “[distributor](http://www.entretemps.asso.fr/maths/Distributors.pdf)”, which is supposed to carry the intuition that a distributor generalizes a functor in a similar way to how a distribution generalizes a function.

[Bénabou](http://cahierstgdc.com/wp-content/uploads/2022/07/F.-BORCEUX-LXIII-3.pdf) in his time introduced the notions of enriched categories, bicategories as well as distributors and invented the term monad. He was lost to us on 11, February 2022 and this library is dedicated to his memory.

Since "profunctor" became the standard nomenclature, we reappropriate "distributor" to describe a profunctor on a [distributive category](https://ncatlab.org/nlab/show/distributive+category).

This library provides a study of `Monoidal` profunctors, `Distributor`s, `Alternator`s and `Filtrator`s. These profunctor constraints are analogous to `Applicative`, `Alternative` and `Filterable` functors.

Examples of `Distributor`s will include printers and parsers, and it will be demonstrated how to write a single term for both.

Profunctors naturally give rise to optics and this library also studies some previously discovered optics, `PartialIso`s, `Monocle`s, `Grate`s and `Wither`s and also defines new optics, `Diopter`s and `Bifocal`s.

Finally, an application of distributors is demonstrated by unifying Backus-Naur form grammars with invertible parsers, giving users a powerful playground for front-end language design.

## previous work

The results concerning invertible parsers are a profunctorial interpretation of [Invertible Syntax Descriptions](https://www.mathematik.uni-marburg.de/~rendel/rendel10invertible.pdf) by Tillman Rendel & Klaus Ostermann.

While `Distributor`s in the library are lax distributive endoprofunctors, a mathematical treatment of strong (i.e. with invertible structure morphisms) distributors is given by Travis Squires in [Profunctors and Distributive Categories](https://central.bac-lac.gc.ca/.item?id=MR31635).

The idea for unifying Backus-Naur grammars with parsers comes from Joachim Breitner in a post [Showcasing Applicative](https://www.joachim-breitner.de/blog/710-Showcasing_Applicative).

The person deserving the most credit for bringing the power of optics to programming is Ed Kmett, to whom I am very grateful for teaching me a lot, with his [lens library](https://github.com/ekmett/lens/).

None of the ideas in this library are particularly original and a lot of related ideas have been explored, in Tom Ellis' [product-profunctors](https://github.com/tomjaguarpaw/product-profunctors) as well as Sjoerd Visscher's [one-liner](https://github.com/sjoerdvisscher/one-liner) and more. Such explorations are _not_ limited to Haskell. Brandon Williams and Stephen Celis' excellent [swift-parsing](https://github.com/pointfreeco/swift-parsing) was also influenced by invertible parser theory.

Some optics in this library are [grates](https://r6research.livejournal.com/28050.html), a new kind of optic, discovered by Russel O'Connor and James Deikun; monocles which are studied by Alexandre Garcia de Oliveira, Mauro Jaskelioff, and Ana Cristina Vieira de Melo in [On Structuring Functional Programs with Monoidal Profunctors](https://arxiv.org/abs/2207.00852); and withers, discovered by Chris Penner in [Composable filters using Witherable optics](https://chrispenner.ca/posts/witherable-optics).

## contributing

We welcome contributors. The [Issues](https://github.com/morphismtech/squeal/issues) page is a good place to communicate.

