include module type of Load_t

type loader

val new_loader : unit -> loader

val load_surface_ast
  : loader
  -> typ:(Surface_ast.Type.lt option)
  -> expr:Surface_ast.Expr.lt
  -> extra_types:(Desugared_ast_kind.maybe_kind Desugared_ast_type_t.t list)
  -> result

val load_file
  : loader
  -> base_path:string
  -> types:(Desugared_ast_kind.maybe_kind Desugared_ast_type_t.t list)
  -> result

(* Return a list of all the files loaded by the loader, in dependency order. *)
val all_files : loader -> (string * result) list
