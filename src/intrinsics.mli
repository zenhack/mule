module D = Ast.Desugared
module R = Ast.Runtime

open Typecheck_types

val values : (unit D.Type.t * R.Expr.t) VarMap.t
val types : (unit D.Type.t) VarMap.t
val kinds : k_var VarMap.t
