include module type of Build_constraint_t
open Typecheck_types

val build_constraints: Ast.Desugared.Expr.t -> built_constraints
val gen_u: bound_target -> [> `Free of tyvar ] UnionFind.var

val make_cops: unit ->
  ( constraint_ops
  * (unify_edge list) ref
  * ((g_node * (u_type UnionFind.var) list) IntMap.t) ref
  )
