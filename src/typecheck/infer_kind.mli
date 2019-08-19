open Ast.Desugared
open Typecheck_types

val unify : u_kind -> u_kind -> u_kind

val infer
  : Build_constraint_t.constraint_ops
  -> k_var VarMap.t
  -> k_var Type.t
  -> k_var Type.t
