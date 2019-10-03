module S = Surface_ast.Expr
module D = Desugared_ast.Expr
module DK = Desugared_ast.Kind

val desugar : S.t -> DK.maybe_kind D.t
