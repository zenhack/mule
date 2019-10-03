include module type of Paths_t

val resolve_embed : here:string -> target:string -> string Lwt.t

val resolve_path : here:string -> target:string -> path
