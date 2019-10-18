open Typecheck_types

let rec gen_kind = function
  | `Arrow(p, r) -> UnionFind.make (`Arrow(gen_kind p, gen_kind r))
  | `Type -> ktype
  | `Row -> krow
  | `Unknown -> gen_k ()

let typecheck exp =
  Desugared_ast.Expr.map exp ~f:gen_kind
  |> Bidir.synth (Bidir.make_initial_context ())
  |> Extract.get_var_type
