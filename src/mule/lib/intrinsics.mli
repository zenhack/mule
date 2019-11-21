module D = Desugared_ast
module R = Runtime_ast

open Common_ast

open Typecheck_types

val values : (Var.t, (k_var D.Type.t * R.Expr.t), Var.comparator_witness) Map.t
val types : (Var.t, k_var D.Type.t, Var.comparator_witness) Map.t
