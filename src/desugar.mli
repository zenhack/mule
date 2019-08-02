module S = Ast.Surface.Expr
module D = Ast.Desugared.Expr
module DK = Ast.Desugared.Kind

val desugar : S.t -> (DK.maybe_kind D.t, MuleErr.t) Result.t
