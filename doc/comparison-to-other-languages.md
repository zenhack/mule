This document describes what is special about Mule, and how it compares
to other languages.

# General

Mule is in the ML-family of programming languages. Accordingly, it
is garbage collected, has a strong type system with good type inference,
and emphasizes immutable data structures and heavy use of higher-order
functions.

Mule's type system is entirely structural ("duck typing"); there is no
way to declare a "new" type in Mule. The point of this is to make coding
against an interface (as opposed to a specific implementation) the
natural thing to do. We don't really lose anything vs nominal typing
either: you can define aliases for types, and the implementation of a
type can be left opaque/private, so you can still enforce abstractions.

Mule is designed for being able to run untrusted code. Accordingly:

* There are no holes in the type system. If an expression type checks,
  you can believe the type, even if you don't trust its author and
  haven't audited the code.
* Mule is referentially transparent (sometimes called "purely
  functional"). This means that most code can't do IO, or even behave
  non-deterministically. The latter provides a useful defense against
  [Spectre][spectre]-style vulnerabilities, as it means most code has no way
  to actually observe timing effects.
* (Planned) Mule's standard libraries are [ocap][ocap] friendly, so
  even when code needs to do some amount of IO to do its job, it is
  still easy and natural to only provide access to what is needed,
  rather than suddenly needing to grant access to everything.

(Planned) Relatedly, Mule is capable of loading code at run time, which
makes it great for writing applications that need "plugins", and for
doing neat things like sending code to a network peer for them to run.

Mule is very much a "one way to do it" language. We strive for
features to be orthogonal and therefore have only one product type
(records), one kind of union/sum/variant, one type of function, one
way to derive boilerplate, to do syntactic abstraction, etc.

# ML family

The ML family of programming languages includes Standard ML, OCaml,
Haskell, Elm, Purescript, and some others. Mule itself falls into this
family, and so it has many similarities with these languages. It differs
from some or all of them in that:

* Mule is referentially transparent ("purely functional") like Elm,
  Haskell and Purescript, and unlike OCaml and Standard ML.
* Mule is strictly evaluated, unlike Haskell but like most other MLs
  (and most other languages).
* As discussed above, Mule's type system is *entirely* structural.
  Our record type is based on the same foundations as Elm's (though it
  is a bit more flexible), but everything else in the language is also
  structural -- unions/sums/variants (which are somewhat like OCaml's
  polymorphic variants), modules (which are just records; see below),
  etc.
* Mule has ML modules like OCaml and SML, in a sense. However, the
  module language and the core language are unified -- modules are
  just records, and functors are just functions. The semantics of
  "functors" in Mule are "generative" like SML, and unlike OCaml's
  "applicative" functors.
* There are no holes in Mule's type system; there is nothing like
  Haskell's `unsafePerformIO` or other generally available unsound
  operations.
* (Planned) Mule will have a lisp-style macro system. We will use this
  to do things that in other MLs have dedicated syntactic sugar (like
  Haskell's do-notation), or require external preprocessors (like
  OCaml's PPX). This will be like Template Haskell in some ways, but
  should be more ergonomic, and macros will not have the ability to do
  arbitrary IO. They will be subject to the same safety constraints as
  the rest of the language.
* Mule does not have type classes, or any other kind of implicit
  overloading mechanism. We may add something later on, but type classes
  would not fit into the language (due to its structural nature). For
  now, the abstractions you might build with type classes in Haskell or
  Purescript can be built by explicitly passing around records. I do not
  believe this approach has been seriously tried in a language designed
  around it, so we should gain some experience before deciding that we
  need to add an additional mechanism to the language.

---

TODO: other comparisons, probably start with lisp dialects...

[ocap]: http://habitatchronicles.com/2017/05/what-are-capabilities/
[spectre]: https://en.wikipedia.org/wiki/Spectre_(security_vulnerability)
