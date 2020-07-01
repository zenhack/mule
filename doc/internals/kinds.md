Mule's kind system is close to System-F Omega, but there is one significant
difference, to restrict recursive types.

Mule has equi-recursive types, and from an algorithmic perspective,
these can arise naturally during constraint solving -- a recursive type
is just a cycle in the type graph. However, when we allow users to write
down types, if we are not careful, they could write down types not
representable as simple graph cycles. For example: `rec a. a` does not
include any nodes, and it's not really clear what it should mean.

We therefore employ a kinding discipline to rule out these cases. The
invariant we want to enforce is that a cycle in the graph is always
broken by at least one ctor node, so `rec a. (a -> int)` is Ok because
the `->` appears between the binding and the use of the recursive
variable.

We split the kinding system into prekinds, guard flags, and kinds.

A kind is a pair of a prekind and a guard flag:

```
kind ::= (guard-flag, prekind)
```

A guard flag is:

```
guard-flag ::= Guarded | Unguarded
```

Prekinds resemble F-Omega kinds, with two differences:

1. The recursive cases are proper kinds, so we have guard flags at each
   level
2. We include rows in addition to the usual `type` kind. This just
   behaves as another unit kind, and isn't terribly interesting.

```
prekind
    ::= type
    | row
    | (kind => kind)
```

Kind constraint solving happens through standard unification, with
variables in place of each sort of node in the tree (kinds, prekinds, and
guards).

The built in type constructors all have kinds returning `Guarded` types.
For example:

```
( -> ) :: ('a, type) => ('b, type) => (Guarded, type)
```

Importantly, no type level built-in has an Unguarded return kind, or one
that is polymorphic in its return kind.

Note that, unlike unification done for types, we *do* perform the occurs
check, as we do not want to admit equi-recursive kinds.

However, we do support equi-recursive *types*, and when a user writes
(rec a. ...), we treat this as a call to a fixed-point type-operator:

```
fix :: ((Unguarded, 'a) => (Guarded, 'a)) => (Guarded, 'a)
```

The kind of the `fix` operator is crucial: because the function's
argument is unguarded, and it is required to return a guarded result, it
_must_ insert at least one constructor node guarding its argument.
Therefore, it can be used to create _cyclic_ types, but not arbitrary
recursive types.
