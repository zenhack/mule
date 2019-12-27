include module type of Typecheck_t

val typecheck
  : get_import_type:(Paths_t.t -> Typecheck_types_t.u_var)
  (* [want] is a list of type annotations to apply to the expression;
   * e.g. if want is `[a; b; c]`, then the expression `e` will be
   * type checked like `(((e : a) : b) : c)`. *)
  -> want:(requirement list)
  -> export:bool
  -> Desugared_ast.Kind.maybe_kind Desugared_ast_expr_t.t
  -> Typecheck_types_t.u_var
