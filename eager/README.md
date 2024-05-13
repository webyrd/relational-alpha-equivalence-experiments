This directory contains experiments with alpha-equivalence,
capture-avoiding-substitution, gensym, etc., all fully relational,
without nominal unification, in an eager context.

By "eager context," I mean that these relations will eagerly ground
their arguments, which can easily result in extremely inefficient
"generate-and-test" behavior.

This code was originally written by William E. Byrd, who was inspired
to revisit this topic during Arunava Gantait's project to implement
the Knuth-Bendix completion algorithm in miniKanren.  This project is
supervised by Professor Madhavan Mukund at Chennai Mathematical
Institute, along with Will Byrd.  Brandon Willard proposed
implementing Knuth-Bendix in miniKanren.  Arunava's work has been
greatly influenced by this [implementation of Knuth-Bendix in
Prolog](https://www.metalevel.at/trs/) by Markus Triska.

Triska's implementation show's off the trick of using fresh logic
variables in a term to represent a "template" containing pattern
variables, then using Prolog's `copy_term` to create a copy of this
template in which the variables can be safely instantiated to perform
pattern matching.  Alas, this technique is non-relational.  Instead of
that technique, I advocated using a different encoding in which
symbols can represent pattern variables.  Thinking about that problem
led me to write this code, which is similar in spirit to other
miniKanren experiments I and others have done over the years, but
which may differ in some of the details.

The point of this experiment is three-fold: (1) to see if
alpha-equivalence, capture-avoiding-substitution, gensym, etc., can be
implemented relationally without nominal unification, using careful
encoding and `=/=`, `absento`, and `symbolo` constraints; (2) to see
if the resulting relations can be usefully applied to existing
relational programs, such as the relational
normalization-by-evaluation code; and (3) to understand better how the
resulting relations might be made lazier using techniques such as
narrowing, residuation, delayed/frozen goals, co-routining, the
Extended Andorra Model of evaluation, etc., inspired by work in
Prolog, Curry, and constraint programming.  This version of the code
is eager, and can serve as a baseline for "generate-and-test"
behavior.

TODO

* Try experiment proposed by Michael Ballantyne on May 11, 2024:
  instead of `capture-avoiding-substo` eagerly performing
  alpha-renaming by calling the eager `alpha-equivo`, add a renaming
  `(x x^)` to an environment that is passed around, and use `absento`
  to ensure `x^` is fresh.

* Try using set constraints from clpset to represent the variable
  bindings.  The original version of clpset doesn't include `absento`,
  though--will probably need an implementation that supports
  `absento`.
