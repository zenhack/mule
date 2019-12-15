This document describes how to build Mule from source.

# Setting up OCaml

Mule itself is implemented in OCaml. The first step to getting set up is
to install OCaml's package manager, [opam][1]. If you already have a
working opam installation, you can skip this section. Most Linux
distributions have a package for it, usually just called `opam`. MacOS
users can install it via [Homebrew][2] (`brew install opam`).

Once opam is installed, set it up with:

```
$ opam init
$ eval $(opam env)
```

For more detailed setup information, see the [official docs][3]

# Installing OCaml dependencies

Next, install the OCaml dependencies for Mule:

```
opam install dune base cmdliner linenoise lwt lwt lwt_ppx mparser \
    pprint ppx_compare ppx_inline_test ppx_let ppx_sexp_conv stdio \
    yojson zarith
```

# Building Mule

To actually compile Mule, run `make`:

```
$ make
```

This will create an executable somewhere in the `./_build` directory.
There is a wrapper script called `mule` at the root of the repository,
which you can use to experiment with mule without installing it:

```
$ ./mule
#mule>
```

To install mule as an opam package, type `make install`. This should put
a `mule` executable in your path.

TODO: talk about MULE_PATH.

[1]: https://opam.ocaml.org
[2]: https://brew.sh
[3]: https://opam.ocaml.org/doc/Install.html
