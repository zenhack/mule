open Ast

val desugar : 'i Surface.Expr.t -> (Error.t, Desugared.Expr.t) OrErr.t
