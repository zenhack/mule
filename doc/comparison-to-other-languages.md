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
  functional"). This has a few advantages:
  * It means that most code can't do IO, or even behave
    non-deterministically. The former drastically reduces attack
    surface, and the latter provides a useful defense against
    [Spectre][spectre]-style side-channel vulnerabilities, as it means
    most code has no way to actually observe timing effects.

    Note that referential transparency is actaully a stronger guarantee
    than is strictly necessary for this property, but also:
  * It will allow us to make use of timeouts, allocation limits, and
    thread cancellation to mitigate denial of service attacks.

    It would be too error prone to do this in a language with
    uncontrolled mutability, because of the possibility of corrupting
    state, so it could only safely happen in such a language at a very
    coarse granularity (possibly whole language VM instances or address
    spaces). By controlling and minimizing state, we make this a practical
    and viable strategy for use at a much finer granularity. See also
    <https://github.com/tc39/proposal-oom-fails-fast#background>
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

(Planned) Mule wants to be a "batteries included" language. It's very
early days, so we aren't there yet -- building out libraries will take
time. But the goal is to have a large, high quality standard library
for developers to draw on.

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

# Lisp family

Mule shares some things with most lisps:

* An emphasis on higher order functions and immutability
* (Planned) the ability to load code dynamically at run-time.
* (Planned) a macro system. The macro system is hygenic, like Scheme
  and unlike Common Lisp and Clojure. We plan to take the hygene a bit
  farther than Scheme does though.

The biggest differences are:

* Mule is statically typed, whereas lisps are generally dynamically
  typed.

  If your only experience with type systems comes from mainstream
  imperative languages like Java and C++, keep an open mind -- Mule's
  type system stays out of your way, while at the same time being much
  more powerful and expressive. It can infer most types without them
  being explicitly written down, so you don't have to sacrifice concision
  to get the benefits.
* Mule is *not* homoiconic; we have dedicated syntax for certain
  constructs (e.g. let, lambda, and match), rather than using data
  literals for everything.  The syntax however is still very minimal,
  and we expect the experience of writing macros won't suffer for it.
  Furthermore, having dedicated constructs for variable binding makes
  macro hygiene simpler; we're able to do scope resolution entirely
  before macro expansion, whereas even in Scheme these steps are
  interleaved, and in non-hygienic systems macro expansion happens
  first.

[ocap]: http://habitatchronicles.com/2017/05/what-are-capabilities/
[spectre]: https://en.wikipedia.org/wiki/Spectre_(security_vulnerability)
