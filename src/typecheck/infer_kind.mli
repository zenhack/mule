open Ast.Desugared

val infer : Kind.t VarMap.t -> 'a Type.t -> [ `Type | `Row ] Type.t
