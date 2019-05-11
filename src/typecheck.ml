let typecheck expr =
  try
    Build_constraint.build_constraints VarMap.empty expr
    |> Solve.solve_constraints
    |> Extract.get_var_type
    |> fun t -> Ok t
  with
    MuleErr.MuleExn e ->
      Error e
