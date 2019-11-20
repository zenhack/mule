This document provides a quick crash course for Mule; it assumes the
reader is already familiar with some ML-family language (which we define
broadly; Haskell, Elm, Scala etc. count, as well as OCaml and Standard
ML obviously).

TODO: finish this

# Basics

Assuming you've successfully built and installed Mule, you can start an
interactive repl by typing `mule`:

```
$ mule
#mule>
```

You can type in expressions, and mule will compute their value and
report their type:

```
#mule> int.add 4 2
6 : int
```

Alternatively, you can evaluate a whole file via `mule eval <filename>`.
The file extension for mule source code is `.mule`.

## Syntax Basics

* Mule is not whitespace sensitive
* End of line comments start with `#`. There are no multi-line comments.
* Everything is an expression; there are no statements, or even
  top-level declarations. A `.mule` source file is one giant expression.

## Integers

Mule's built-in `int` type is an arbitrary precision integer; there are
no limits on the size of the values it can hold, except for memory
usage:

```
#mule> 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : int
```

Mule's integer literals can be written in decimal, hexidecimal, binary
or octal:

```
#mule> 16
16 : int
#mule> 0x10
16 : int
#mule> 0b10000
16 : int
#mule> 0o20
16 : int
```

Negative integers start with a minus sign:

```
#mule> -42
-42 : int
```

Positive integers may optional have a leading plus sign:

```
#mule> +42
42 : int
```

Mule allows underscores in the middle of integer literals to improve
readability:

```
#mule> 1_000_000_000
1000000000 : int
```

We don't yet have infix operators, so you have to call the integer
operations using the usual function syntax (explored later):

```
#mule> int.mul 2 2
4 : int
```

## Text

Mule's built in `text` type (often called a "string" in other
languages) is enclosed in double quotes:

#mule> "Hello, World!"
"Hello, World!" : text

Right now the `text` type maps to a flat array of memory (javascript
strings on the js backend, or ocaml strings in the interpreter), but
longer term we want to move to a smarter data structure, with efficient
concatenation etc, So you will be able to glue large text values
together without having to do anything special to avoid an O(n) cost for
each append.

## Built in types

Mule has several built-in primitive types:

* integers
* characters
* text (called "strings" in many other languages).

