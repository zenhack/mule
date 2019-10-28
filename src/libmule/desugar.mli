module S = Surface_ast.Expr
module ST = Surface_ast.Type
module D = Desugared_ast.Expr
module DT = Desugared_ast.Type
module DK = Desugared_ast.Kind

val desugar : S.lt -> DK.maybe_kind D.t
val desugar_type : ST.lt -> DK.maybe_kind DT.t
