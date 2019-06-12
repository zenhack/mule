module D = Ast.Desugared
module R = Ast.Runtime

val values : (unit D.Type.t * R.Expr.t) VarMap.t
val types : (unit D.Type.t) VarMap.t
