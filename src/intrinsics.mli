module D = Desugared_ast
module R = Runtime_ast

open Typecheck_types

val values : (k_var D.Type.t * R.Expr.t) VarMap.t
val types : (k_var D.Type.t) VarMap.t
