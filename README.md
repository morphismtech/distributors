# distributors


## introduction
The term "distributor" is a synonym for ["profunctor"]
(https://ncatlab.org/nlab/show/profunctor).
Jean Bénabou who invented the term and originally used
“profunctor,” then preferred [“distributor,”]
(http://www.entretemps.asso.fr/maths/Distributors.pdf)
which is supposed to carry the intuition that a distributor
generalizes a functor in a similar way to how a distribution
generalizes a function.

[Bénabou]
(http://cahierstgdc.com/wp-content/uploads/2022/07/F.-BORCEUX-LXIII-3.pdf)
in his time introduced the notions of enriched categories,
bicategories as well as distributors and invented the term monad.
He was lost to us on 11, February 2022
and this library is dedicated to his memory.

Since "profunctor" became the standard nomenclature,
we reappropriate "distributor" to describe a profunctor
on a [distributive category]
(https://ncatlab.org/nlab/show/distributive+category).

This library provides a study of such profunctors,
alongside `Monoidal` profunctors,
as well as `Choice` and `Cochoice` profunctors.
These classes of profunctors are analogous to
`Alternative`, `Applicative` and `Filterable` functors.

Examples of `Distributor`s will include printers and parsers,
and it will be demonstrated how to write a single term for both.
The results here are a profunctorial interpretation of
[Invertible Syntax Descriptions]
(https://www.mathematik.uni-marburg.de/~rendel/rendel10invertible.pdf)

A `Distributor` is a lax distributive endoprofunctor
on the category of Haskell types and functions.
A mathematical treatment of strong distributors is given by
Travis Squires in [Profunctors and Distributive Categories]
(https://central.bac-lac.gc.ca/.item?id=MR31635)
