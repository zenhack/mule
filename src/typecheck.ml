open Typecheck_types

let rec gen_kind = function
  | `Arrow(p, r) -> UnionFind.make (`Arrow(gen_kind p, gen_kind r))
  | `Type -> kvar_type
  | `Row -> kvar_row
  | `Unknown -> gen_k ()

let typecheck expr =
  Desugared_ast.Expr.map expr ~f:gen_kind
  |> Build_constraint.build_constraints
  |> Solve.solve_constraints
  |> Extract.get_var_type
