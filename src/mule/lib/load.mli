include module type of Load_t

val load_surface_ast
  : typ:(Surface_ast.Type.lt option)
  -> expr:Surface_ast.Expr.lt
  -> extra_types:(Desugared_ast_kind.maybe_kind Desugared_ast_type_t.t list)
  -> result

val load_file
  : base_path:string
  -> types:(Desugared_ast_kind.maybe_kind Desugared_ast_type_t.t list)
  -> result
