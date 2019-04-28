open Typecheck_types

(** Evaluate a type level term to weak-head normal form. *)
val whnf: u_type -> u_type
