let typecheck expr =
  let env = Map.map ~f:fst Intrinsics.intrinsics in
  try
    Build_constraint.build_constraints env expr
    |> Solve.solve_constraints
    |> Extract.get_var_type
    |> fun t -> Ok t
  with
    MuleErr.MuleExn e ->
      Error e
