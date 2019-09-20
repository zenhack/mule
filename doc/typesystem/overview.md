This document provides a guide to understanding Mule's type system from
an implementer's or theorist's perspective. It is not intended to be a
good resource for learning how to *use* Mule, but will be important for
anyone wanting to hack on the type checker.

This document is not self contained. Rather, it points to papers that
explain ideas drawn from elsewhere, and directly describes our own
additions. It would be nice to have a condensed description of the type
system, but this will have to do for the short term.

# MLF

The backbone of Mule's type system is [MLF][1], specifically the graph
based presentation. There are several relevant papers; if you're not
familiar with that body of work I recommend starting with [Gabriel
Scherer's internship report][2]. The xMLF stuff is not immediately
relevant to Mule currently, though it may be of interest down the line.

We deviate from the core algorithms in a few ways, which we document
here.

## Higher kinds

While we borrow beta reduction from MLF-Omega, we don't borrow
explicit type abstraction as-is. TODO: describe the details.

## Q nodes

Rather than having quantifiers for binding edges be implicitly above
the node to which the binding points, We introduce explicit Q nodes,
which serve as a place to anchor binding edges. Our type equivalence
relation makes it legal to insert an inert Q node just above any other
node. This is basically a graph analog of a rule like:

```
if
    a not in ftv(T)
then
    T = all a. T
```

The unification algorithm works as normal, except that if we find
ourselves trying to unify a Q node with something other than a Q node,
we first insert a Q-node above the non-Q node, and then unify with that.

This has a couple nice benefits:

* It brings the surface syntax and the graph representation closer
  together, by giving a direct analog of quantifiers. This results
  in fewer awkward cases when translating between syntax and graphs.
  For example, In the original MLF presentation, the graph
  representation for the type `all a. a` is not obvious -- doing the
  translation naively would result in a node bound on itself! Adding
  the Q node makes this straightforward.
* As a side effect of binding all variables on Q-nodes, we now have a
  guarantee that constructor nodes (functions, etc). Are always inert,
  which makes some things easier to reason about.

## Recursive types

Mule allows equi-recursive types. A recursive type is really just a
cycle in the graph. Algorithmically, this basically amounts to:

1. skipping the occurs check
2. accounting for the possibility of cycles in other code manipulating
   the graph.

This may actually endanger principality, since the original argument as
to why the graph based MLF presentation has principal types depends on
the graphs being acyclic. It would be good to explore this and better
understand the consequences.

Note that we do not allow polymorphic recursion; recursive types are
required to be of kind `type`.

# Rows

Mule has row-polymorphic records and sums. They are based on [this
paper][3]. The biggest deviations from the original are:

1. We do not treat duplicate labels as significant. {l : a, l : b} is the
   same type as {l : a}.
2. We do not allow field deletion (which is obviously required for (1)
   to be sound).

The paper does not talk about row-polymorphic sums, but they are a
fairly straightforward application of the same notion of rows.

The way we do records is slightly different to account for associated
types (TODO: discuss).

[1]: http://gallium.inria.fr/~remy/work/mlf/
[2]: http://gallium.inria.fr/~remy/mlf/scherer@master2010:mlfomega.pdf
[3]: https://www.microsoft.com/en-us/research/publication/extensible-records-with-scoped-labels/
