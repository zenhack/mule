open Ast

val desugar : Surface.Expr.t -> (Error.t, Desugared.Expr.t) OrErr.t
