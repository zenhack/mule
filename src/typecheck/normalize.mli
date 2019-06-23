(* This module provides support for "normalizing" types, according to the
 * type system's equivalence rules.
 *)
open Typecheck_types

(* Reduce the term inside the variable to normal form. *)
val nf : u_var -> u_var

(* Normalize two types with respect to each other, up to whnf.
 *
 * The exact form they are reduced to is dependent on *both* terms, but they
 * will be close enough to one another for the unification logic to do its
 * thing correctly.
 *
 * In some instances, a solution to this is a bit more natural than a single
 * normal form for an individual term.
 *)
val pair : u_var -> u_var -> (u_var * u_var)
