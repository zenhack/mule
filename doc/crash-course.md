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
and backslashes must be escaped by preceding them with a backslash. So:

* `\"` generates a double quote.
* `\\` generates a single backslash

Additionally, the following escape sequences exist (though you can also
just use the literal character for each of these):

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
* The body of the function, which is an expression.

We'll see later that the parameters can be any "pattern," not just
variables, but for now we'll assume they are variables. Legal variable
names must:

* Start with a lower case letter or underscore
* Consisit of only letters, numbers, and the characters `_`, `-`, `!`,
  and `?`.
* Right now identifiers are ascii-only. Eventually we will likely allow
  any unicode letter, to support developers who speak languages other
  than English.

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

And the expression:

```
f x y
```

Is equivalent to:

```
(f x) y
```

## Unions

Like most ML dialects, mule supports (tagged) union types. Unlike
most ML dialects, you don't have to declare them anywhere (somewhat like
OCaml's polymorphic variants).  A union tag starts with an uppercase
letter, and otherwise allows the same characters as variable names.

```
#mule> SomeTaggedValue 4
it : SomeTaggedValue int =
  SomeTaggedValue 4
#mule> ATagIJustMadeUp "hello"
it : ATagIJustMadeUp text
  ATagIJustMadeUp
```

Currently tags always accept exactly one argument. This will probably
change in the future, to allow zero or multiple arguments.

## Match expressions

If you've been following along in the repl thus far, you may now want to
switch to editing a `.mule` source file and running `mule eval`, as our
expressions are about to get bigger, and we'll want more than one line
to work with.

Unions are most useful when combined with the match expression, a
cornerstone of the ML family. In Mule it looks like this:

```
match ValueToLookAt "Hello" with
| UnViewable n -> int.add n 4
| ValueToLookAt "Goodbye" -> 0
| ValueToLookAt t -> text.length t
end
```

That is, it takes the form:

```
match <expression> with
| <pattern> -> <expression>
| <pattern> -> <expression>
| ...
end
```

The first pipe is optional, so if you have a short list of patterns you
can do:

```
match x with Left y -> y | Right z -> z end
```

Patterns can be any of:

* A variable name
* A tag applied to another pattern
* A constant literal, like `"hello"`, `4`, `'x'`
* The wildcard pattern `_`

In terms of evaluation, match expressions work the same way they do in
other ML dialects: The first expression is compared against the
patterns, and the whole match expression evaluates to the expression
in the first branch that matches. Inside the expression, any variables
in the pattern are bound to the corresponding part of the value.

Mule will insist that the patterns in a match are exhaustive, so for
example, this will be rejected:

```
match x with
| 1 -> "one"
| 2 -> "two"
end
```

## Let expressions

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

There is no special syntax for defining functions; just use a `let` and
a lambda:

```
let double = fn n. int.add n n in
double 7
```

You can define more than one variable in the same let expression,
separating the definitions with commas:

```
let sender = "alice", receiver = "bob" in ...
```

When splitting let bindings across multiple lines, the convention in
mule is to put commas *in front* of the definitions, at the beginning of
the line, rather than after them at the end.  To make editing lists of
bindings easier, a leading comma is allowed before the first binding:

```
let
  , sender = "alice"
  , receiver = "bob"
in
...
```

The comma-first style may seem bizzare if you've never encountered it
before, but from experience in other languages where this is common,
I've found it improves readability -- it's much easier to spot a missing
comma. Think of it as a bulleted list if that helps you.

In general, wherever commas are used as separators in Mule, a leading
comma is permitted.

Let expressions create (mutually) recursive bindings, so these are
legal:

```
let length =
  fn list. match list with
    | Nil _ -> 0
    | Cons l -> 1 + length l.tail
  end
in
length (Cons { head = 'x', tail = Nil {} })
```

```
let
  , even =
      fn n. match n with
        | 0 -> True {}
        | _ -> odd (int.sub n 1)
      end
  , odd =
      fn n. match n with
        | 0 -> False {}
        | _ -> even n
      end
in
even 2
```

## Records

Records are used to group multiple values. Example:

```
#mule> { age = 34, name = "Alice" }
it : {name : text, age : int} =
  {age = 34, name = "Alice"}
```

You can access individual fields using the dot (`.`) operator:

```
#mule> { age = 34, name = "Alice" }.name
it : text =
  "Alice"
```

You can create a modified copy of the record, with fields added or
replaced, using `where`. This:

```
let alice = { age = 34, name = "Alice" } in
alice where { age = 39 }
```

...results in:

```
it : {name : text, age : int} =
  { age = 39, name = "Alice }
```

You can add fields. This:

```
let alice = { age = 34, name = "Alice" } in
alice where { favorite-color = "blue" }
```

Yields:

```
it : {favorite-color : text, name : text, age : int} =
  {age = 34, favorite-color = "blue", name = "Alice"}
```

You can also change the type of an existing field:

```
let alice = { age = 34, name = "Alice" } in
alice where { name = { first = "Alice", last = "Smith" } }
```

...giving:

```
it : {name : {last : text, first : text}, name : text, age : int} =
  {age = 34, name = {first = "Alice", last = "Smith"}}
```

Note that the fields to update (after the `where`) must be a record
*literal*; the following is not allowed:

```
let
  , alice = { age 34, name = "Alice" }
  , extra-info = { favorite-color = "blue" }
in
alice where extra-info
```

The field names in a record can be defined reursively, or refer to one
another, like in a let binding:

```
{
  , even =
      fn n. match n with
        | 0 -> True {}
        | _ -> odd (int.sub n 1)
      end
  , odd =
      fn n. match n with
        | 0 -> False {}
        | _ -> even n
      end
}
```

## Import

So far we've been working within a single file (or at the repl). As
programs get bigger, we'll want to split them up.

The `import` expression imports the value defined in another source
file. Given the files `big-number.mule`:

```
1_000_000_000_000
```

...and `bigger-number.mule`:

```
import "./big-number" + 1
```

the latter will evaluate to:


```
1000000000001
```

`import` takes a string literal. Imports can be used anywhere in an
expression, but the contents of a given file are only ever evaluated
once, and the import happens at compile time, not dynamically.

The file referenced by the import is located as follows:

- If the string starts with `./`, it is treated as a path relative to
  the file containing the import expression. The suffix `.mule` is added
  to the path to locate the actual file.
- If the string does *not* start with `./`, and the first path segment
  contains a dot, it is assumed to be a third party package, and the
  source file is expected to be found at
  `${MULE_PATH}/<import path>.mule`, or `~/mule-src/<import path>.mule`
  if the `MULE_PATH` environment variable is not defined. For example,
  `import "example.org/alice/crypto"` imports the file
  `${MULE_PATH}/example.org/alice/crypto.mule`. Eventually we will have
  a package manager that fetches third party packages based on URL, but
  for now you have to put things in `MULE_PATH` yourself.
- Otherwise, the path is assumed to be part of the standard library.
  If the environment variable `MULE_ROOT` is defined, mule will look
  there, otherwise it will look in a location determined at install
  time.

The set of characters allowed in import paths is limited to lowercase
ascii letters, digits, `'.'`, `'-'`, and `'_'`. The path segment `".."`
is not allowed.

Most of the time, the value defined in a file will be a record. For
example:

```
#mule> import "maybe"
it : {
  , type cmd a = <type lambda> a
  , type t b = Some b | None {}
  , then : all c d. <type lambda> c -> (c -> <type lambda> d) -> <type lambda> d
  , flatten : all e. <type lambda> (<type lambda>) e -> <type lambda> e
  , just : all f. f -> <type lambda> f
  , map : all g h. (g -> h) -> <type lambda> g -> <type lambda> h
  , with-default : all i. i -> <type lambda> i -> i
  } =
  {
  , flatten = <lambda>
  , just = <lambda>
  , map = <lambda>
  , then = <lambda>
  , with-default = <lambda>
  }
```

The above contains some things we haven't talked about yet (chiefly
associated types); we'll get to that. But for now, observe that we
can use the import expression and a let binding to use this record
much like we would a module in another language:

```
let maybe = import "maybe" in
maybe.with-default "no value" (None {})
```

Note that the functions we've been using like `int.add` are actually
themselves stored in records; to find out what other functions are
available from the int "module," you can ask the repl:

```
#mule> int
it : {
  , type t = int
  , add : int -> int -> int
  , sub : int -> int -> int
  , mul : int -> int -> int
  , div : int -> int -> int
  , rem : int -> int -> int
  , compare : int -> int -> (LT {} | GT {} | EQ {})
  } =
  {
  , add = <primitive-function>
  , compare = <primitive-function>
  , div = <primitive-function>
  , mul = <primitive-function>
  , rem = <primitive-function>
  , sub = <primitive-function>
  }
```

This is also true of the other "modules" we've seen, like `text` and
`char`.

## Embed

Related to `import` is `embed`. Embed allows you to embed the raw text
of another file into your program, as a string literal. For example:


```
$ echo 'Hello, World!' > hello.txt
$ mule
#mule> embed "./hello.txt"
it : text =
  "Hello, World!\n"
```

This is occasionally a useful feature on its own, but is most useful
when combined with macros (which we've not yet discussed, and aren't
actually implemented yet at the time of writing).

Legal values for the embed path are the same as for import, except that
only the relative version (starting with `./`) is allowed.
