include module type of Load_t

type loader

val new_loader : unit -> loader

val load_surface_ast
  : loader
  -> expr:Surface_ast.Expr.lt
  -> extra_types:(Typecheck_t.requirement list)
  -> result

val load_file
  : loader
  -> base_path:string
  -> types:(Typecheck_t.requirement list)
  -> result

(* Return a list of all the files loaded by the loader, in dependency order. *)
val all_files : loader -> (string * result) list
