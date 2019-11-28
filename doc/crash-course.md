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
it : int =
  6
```

The above reports that the result has type `int`, and the value is `6`.

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
it : int =
  100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
```

Mule's integer literals can be written in decimal, hexidecimal, binary
or octal:

```
#mule> 16
it : int =
  16
#mule> 0x10
it : int =
  16
#mule> 0b10000
it : int =
  16
#mule> 0o20
it : int =
  16
```

Negative integers start with a minus sign:

```
#mule> -42
it : int =
  -42
```

Positive integers may optionally have a leading plus sign:

```
#mule> +42
it : int =
  42
```

Mule allows underscores in the middle of integer literals to improve
readability:

```
#mule> 1_000_000_000
it : int =
  1000000000
```

We don't yet have infix operators, so you have to call the integer
operations using the usual function syntax (explored later):

```
#mule> int.mul 2 2
it : int =
  4
```

## Text

Mule's built in `text` type (often called a "string" in other
languages) is enclosed in double quotes:

```
#mule> "Hello, World!"
it : text =
  "Hello, World!"
```

Inside of text literals, any character is allowed, but double quotes
backslashes must be escaped by preceding them with a backslash. So:

* `\"` generates a double quote.
* `\\` generates a single backslash

Additionally, the following escape sequences exist (though you can also
just use the literal character for each of these:

* `\'` for single quote.
* `\n` for newline.
* `\t` for tab.
* `\r` for carriage return.

Right now the `text` type maps to a flat array of memory (JavaScript
strings on the JavaScript backend, or OCaml strings in the interpreter),
but longer term we want to move to a smarter data structure, with
efficient concatenation etc, So you will be able to glue large text
values together without having to do anything special to avoid an O(n)
cost for each append.

## Characters

Mule also has a built in `char` type, which represents a single
character. The syntax is the same as for `text`, except we use single
quotes instead of double, and only one character is allowed:

```
#mule> 'c'
it : char =
  'c'
```

The same escape sequences are available as with text, though in this
case the single-quote escape is mandatory while the double quote is
optional, so you can write `'"'` for a double quote character literal.

## Functions

In mule, a lambda looks like:

```
#mule> fn x y. x
it : all a. (a) -> all b. (b) -> a =
  <lambda>
```

That is:

* The keyword `fn`
* A list of parameters (in this case `x y`)
* A dot `.`
* The body of the expression, which is a function.

You'll notice that the repl won't display the details of a function;
instead, it will just say `<lambda>`. It will still give you the type
however. There are a few other sorts of value that will do something
similar.

Functions are applied to their arguments by listing them separated by
whitespace:

```
#mule> (fn x y. x) 1 2
it : int =
  1
```

Like in many ML family languages, the multi-argument syntax is just
syntactic sugar for currying, so the expression:

```
fn x y. x
```

Is equivalent to:

```
fn x. fn y. x
```

## Let expressions

If you've been following along in the repl thus far, you may now want to
switch to editing a `.mule` source file and running `mule eval`, as our
expressions are about to get bigger, and we'll want more than one line
to work with.

Let expressions can be used to bind the value of an expression to a
variable, which can be used in the body of the let. The most basic
version of the syntax is:

```
let <variable> = <expresssion> in <expression>
```

Let's try out an example. Put this in a file (let's call it
`scratch.mule`):

```
# scratch.mule
let increment = int.add 1 in
increment 4
````

...and run it with `mule eval ./scratch.mule`.

You should see this output:

```
it : int =
  5
```

Legal variable names must:

* Start with a lower case letter or underscore
* Consisit of only letters, numbers, and the characters `_`, `-`, `!`,
  and `?`.
* Right now identifiers are ascii-only. Eventually we will likely allow
  any unicode letter, to support developers who speak languages other
than English.
