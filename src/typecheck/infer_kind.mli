open Ast.Desugared
open Typecheck_types

val infer : k_var VarMap.t -> k_var Type.t -> k_var Type.t
