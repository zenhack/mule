open Typecheck_types
open Desugared_ast

val get_var_type: u_var -> int Type.t

val get_var_row: u_var -> int Type.row
