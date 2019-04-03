open Ast.Desugared

val infer : Kind.t VarMap.t -> 'a Type.t -> Kind.t Type.t
