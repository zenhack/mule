open Typecheck_types

val unify: u_type -> u_type -> u_type
val unify_row: u_row -> u_row -> u_row
val unify_bound: bound_target bound -> bound_target bound -> bound_target bound
