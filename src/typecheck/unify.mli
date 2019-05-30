open Typecheck_types

val unify: u_type -> u_type -> u_type
val unify_bound: bound_target bound -> bound_target bound -> bound_target bound

val normalize_unify: u_var -> u_var -> unit
