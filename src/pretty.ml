open Ast
open Ast.Desugared

let typ t = Sexp.to_string_hum (Type.sexp_of_t (fun _ -> sexp_of_unit ()) t)
let expr e = Sexp.to_string_hum (Expr.sexp_of_t (fun _ -> sexp_of_unit ()) e)
let runtime_expr e = Sexp.to_string_hum (Runtime.Expr.sexp_of_t e)
