# play
##A Logic Programming Playground for Lambda Terms, Combinators, Types and Tree-based Arithmetic Computations

With sound unification, Definite Clause Grammars and compact expression of combinatorial generation algorithms, logic programming is shown to conveniently host a declarative playground where interesting properties and behaviors emerge from the interaction of heterogenous but deeply connected computational objects. 

Compact combinatorial generation algorithms are given for several families of lambda terms, including open, closed, simply typed and linear terms as well as type inference and normal order reduction algorithms. We describe a Prolog-based combined lambda term generator and type-inferrer for closed well-typed terms of a given size, in de Bruijn notation. 

We introduce a compressed de Bruijn representation of lambda terms and define its bijections to standard representations. Our compressed terms facilitate derivation of size-proportionate ranking and unranking algorithms of lambda terms and their inferred simple types. 

The S and K combinator expressions form a well-known Turing-complete subset of the lambda calculus. We specify evaluation, type inference and combinatorial generation algorithms for SK-combinator trees. In the process, we unravel properties shedding new light on interesting aspects of their structure and distribution. 

A uniform representation, as binary trees with empty leaves, is given to expressions built with Rosser's X-combinator, natural numbers, lambda terms and simple types. Using this shared representation, ranking/unranking algorithm of lambda terms to tree-based natural numbers are described. 

Our algorithms, expressed as an incrementally developed literate Prolog program, implement a declarative playground for exploration of representations, encodings and computations with uniformly represented lambda terms, types, combinators and tree-based arithmetic.
