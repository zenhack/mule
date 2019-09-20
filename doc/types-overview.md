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

[1]: http://gallium.inria.fr/~remy/work/mlf/
[2]: http://gallium.inria.fr/~remy/mlf/scherer@master2010:mlfomega.pdf
