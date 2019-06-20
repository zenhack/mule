open Ast.Desugared

val infer : Kind.maybe_kind VarMap.t -> 'a Type.t -> Kind.t Type.t
