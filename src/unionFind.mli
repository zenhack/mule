(* Union find/disjoint sets data structure:
 *
 * https://en.wikipedia.org/wiki/Disjoint-set_data_structure
 *
 * We call the sets "unification variables" (or just [var]). Each set has an
 * associated value.
*)

(* A set (or unification variable). *)
type 'a var

(* Make a new set with the given value. *)
val make : 'a -> 'a var

(* Get the value of the set. *)
val get : 'a var -> 'a

(* Set the value of the set. *)
val set : 'a -> 'a var -> unit

(* Update the value of the set. *)
val modify : ('a -> 'a) -> 'a var -> unit

(* Compare two variables for equality *)
val equal : 'a var -> 'a var -> bool

(* Unify two variables, given a function to merge their values. The variables
 * will not appear merged until the function returns.
 *
 * merge is reentrancy-safe, in that no invariants are broken by passing a
 * variable to merge that is in use by an existing call to merge (higher up
 * in the stack), but note that the final value will follow a "last update
 * wins" rule. It is *not* concurrency safe.
*)
val merge
  : ('a -> 'a -> 'a)
  -> 'a var
  -> 'a var
  -> unit
