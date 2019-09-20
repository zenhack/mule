This document is the beginning of an attempt to centrally document &
formalize mule's type system. It is very much a WIP.

The notation is an adjustment of the usual notation used in the type
theory literature, adapted to be reasonable to write in ascii.

# Abstract Syntax

## quantifiers

```
q ::=
	all
	exist
```

## types

```
T ::=
	q tv. T
	tv
	{ T }
	+ T
	T -> T
	<>
	< l : T | T >
	lam tv. T
	T T
```

## type variables

```
tv ::=
	a
	b
	c
	...
```

## kinds

```
K ::=
	type
	row
	K => K
```

# Shorthands

```
	< l1 : T1, l2 : T2 |  T >
desugars to
	< l1 : T1 | < l2 : T2 | T > >
```


# Type Equivalence

Mule has a fairly rich type equivalence relation.

## Structural rules

These just capture that the relation is in fact an equivalence relation.

Reflexivity:

```
if
then
	T = T
```

Symmetry:

```
if
	T1 = T2
then
	T2 = T1
```

Transitivity:

```
if
	T1 = T2
	T2 = T3
then
	T1 = T3
```

## Quantifiers

```
if
	a not in ftv(T)
then
	q a. T = T
```

```
if
then
	q a. q b. T = q b. q a. T
```

```
if
	b not in ftv(T)
then
	q a. T = q b. T[a |-> b]
```

## Rows

```
if
	T1 = T2
then
	< l : T1 | T > = < l : T2 | T >
```

```
if
	T1 = T2
then
	< l : T | T1 > = < l : T | T2 >
```

```
if
	l1 /= l2
then
	< l1 : T1, l2 : T2 | T > = < l2, T2 : l1, T1 | T >
```

Shadowed labels may be dropped. This one is new vs. {Records}, and is
only sound because we don't allow removing fields:

```
if
then
	< l : T1, l : T2 | T > = < l : T1 | T >
```

## Beta reduction

```
if
	T1 = T2
then
	T1 T = T2 T
```

```
if
	T1 = T2
then
	T T1 = T T2
``

```
if
	T1[a -> T2] = T3
then
	(lam a. T1) T2 = T3
```

## Recursive types

```
if
then
	(rec a. T) = (lam a. T) (rec a. T)
```
