let typecheck expr =
  try
    Ast.Desugared.Expr.map expr ~f:(fun _ -> Typecheck_types.gen_k ())
    |> Build_constraint.build_constraints
    |> Solve.solve_constraints
    |> Extract.get_var_type
    |> fun t -> Ok t
  with
    MuleErr.MuleExn e ->
      Error e
