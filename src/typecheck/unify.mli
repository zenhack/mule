open Types
open Typecheck_types

val unify: reason -> u_type -> u_type -> u_type
val unify_bound: reason -> bound_target bound -> bound_target bound -> bound_target bound

val normalize_unify: reason -> u_var -> u_var -> unit
