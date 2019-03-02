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

(* Unify two variables, given a function to merge their values. As soon as this
 * function is called, the variables are considred unified; even if the funtion
 * returns [Err], the variables are now considered the same.
 *)
val merge
  : ('a -> 'a -> 'a)
  -> 'a var
  -> 'a var
  -> unit
