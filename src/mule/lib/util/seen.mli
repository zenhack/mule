(* This module provides support for traversing graphs, and memoizing results
   for individual nodes. *)
type ('k, 'v) t

(* Make a new memozing map. *)
val make : ('k, 'cmp) Map.comparator -> ('k, 'v) t

(* Return the value associated with the key, using the provided function to
   compute it if not present. *)
val get : ('k, 'v) t -> 'k -> (unit -> 'v) -> 'v

(* Using the provided function to compute the value associated with the
   given key, if it is not present. Unlike [get], this works correctly
   if called reentrantly. *)
val guard : ('k, 'v) t -> 'k -> (unit -> 'v) -> unit
