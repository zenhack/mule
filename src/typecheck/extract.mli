open Typecheck_types
open Ast.Desugared

val get_var_type: u_type UnionFind.var -> int Type.t
