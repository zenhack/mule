module D = Ast.Desugared
module R = Ast.Runtime

open Typecheck_types

val values : (k_var D.Type.t * R.Expr.t) VarMap.t
val types : (k_var D.Type.t) VarMap.t
