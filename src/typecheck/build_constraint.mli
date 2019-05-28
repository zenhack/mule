include module type of Build_constraint_t
open Typecheck_types
open Ast.Desugared

val build_constraints: unit Type.t VarMap.t -> Expr.t -> built_constraints

val make_cops: unit ->
  ( constraint_ops
    * (unify_edge list) ref
    * ((g_node * (u_type UnionFind.var) list) IntMap.t) ref
  )
