include module type of Paths_t

val resolve_embed : here:string -> loc:Common_ast.Loc.t -> target:string -> string

val resolve_path : here:string -> loc:Common_ast.Loc.t -> target:string -> path
