include module type of Build_constraint_t
open Typecheck_types
open Ast.Desugared

val build_constraints: k_var Expr.t -> built_constraints

val make_cops: unit ->
  ( constraint_ops
    * (unify_edge list) ref
    * ((g_node * u_var list) IntMap.t) ref
    * (Types.reason * k_var * k_var) list ref
  )
