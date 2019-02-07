open OrErr
module S = Set.Make(String)

(* Free variables in an expression *)
let rec free_vars env = Ast.Surface.Expr.(
  function
  | Var (_, Ast.Var v) ->
      if S.mem v env then
        S.empty
      else
        S.singleton v
  | Lam (_, Ast.Var v, body) ->
      free_vars (S.add v env) body
  | App (_, f, x) ->
      S.union (free_vars env f) (free_vars env x)
  | Record (_, fields) ->
      fields
        |> List.map (fun (_, v) -> free_vars env v)
        |> List.fold_left S.union S.empty
  | GetField(_, e, _) ->
      free_vars env e
  | Ctor _ ->
      S.empty
)

let check_unbound expr =
  let free = free_vars S.empty expr in
  match S.find_first_opt (fun _ -> true) free with
  | Some x -> Err (Error.UnboundVar (Ast.Var x))
  | None -> Ok ()
