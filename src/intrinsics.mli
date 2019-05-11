module D = Ast.Desugared
module R = Ast.Runtime

val intrinsics : (unit D.Type.t * R.Expr.t) VarMap.t
