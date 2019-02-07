open OrErr
open Ast.Surface.Expr
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
  | Record (_, fields) -> fields_free_vars env fields
  | Update(_, e, fields) ->
      S.union
        (free_vars env e)
        (fields_free_vars env fields)
  | GetField(_, e, _) ->
      free_vars env e
  | Ctor _ ->
      S.empty
)
and fields_free_vars env fields =
  fields
    |> List.map (fun (_, v) -> free_vars env v)
    |> List.fold_left S.union S.empty

(* Check for unbound variables. *)
let check_unbound_vars expr =
  let free = free_vars S.empty expr in
  match S.find_first_opt (fun _ -> true) free with
  | Some x -> Err (Error.UnboundVar (Ast.Var x))
  | None -> Ok ()

(* Check for duplicate record fields *)
let check_duplicate_record_fields =
  let rec go =
    let rec check_fields all dups = function
      | (Ast.Label x, v) :: xs ->
          go v >>
          if S.mem x all then
            check_fields all (S.add x dups) xs
          else
            check_fields (S.add x all) dups xs
      | [] ->
          if S.is_empty dups then
            Ok ()
          else
            Err
              ( Error.DuplicateFields (List.of_seq (S.to_seq dups))
              )
    in
    function
    | Record (_, fields) ->
        check_fields S.empty S.empty fields
    | Update(_, e, fields) ->
        go e
        >> check_fields S.empty S.empty fields

    (* The rest of this is just walking down the tree *)
    | Lam (_, _, body) -> go body
    | App (_, f, x) -> go f >> go x
    | GetField(_, e, _) -> go e

    | Var _ -> Ok ()
    | Ctor _ -> Ok ()
  in go

let check expr =
  check_unbound_vars expr
  >> check_duplicate_record_fields expr
