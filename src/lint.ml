open OrErr
open Ast.Surface.Expr
module S = Set.Make(String)
module LSet = Set.Make(Ast.Label)

(* Free variables in an expression *)
let rec free_vars env = Ast.Surface.Expr.(
  function
  | Var (_, Ast.Var v) ->
      if S.mem v env then
        S.empty
      else
        S.singleton v
  | Lam (i, (pat :: pats), body) ->
      case_free_vars env (pat, (Lam (i, pats, body)))
  | Lam (_, [], body) ->
      free_vars env body
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
  | Match (_, e, cases) ->
      List.fold_left
        S.union
        (free_vars env e)
        (List.map (case_free_vars env) cases)
)
and case_free_vars env (p, body) =
  match p with
    | Ast.Surface.Pattern.Wild _ ->
        free_vars env body
    | Ast.Surface.Pattern.Var(_, Ast.Var v) ->
        free_vars (S.add v env) body
    | Ast.Surface.Pattern.Ctor (_, _, p') ->
        case_free_vars env (p', body)
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
      | (x, v) :: xs ->
          go v >>
          if LSet.mem x all then
            check_fields all (LSet.add x dups) xs
          else
            check_fields (LSet.add x all) dups xs
      | [] ->
          if LSet.is_empty dups then
            Ok ()
          else
            Err
              ( Error.DuplicateFields (List.of_seq (LSet.to_seq dups))
              )
    in
    let rec check_cases = function
      | [] -> Ok ()
      | ((_, body) :: cs) -> go body >> check_cases cs
    in
    function
    | Record (_, fields) ->
        check_fields LSet.empty LSet.empty fields
    | Update(_, e, fields) ->
        go e
        >> check_fields LSet.empty LSet.empty fields

    (* The rest of this is just walking down the tree *)
    | Lam (_, _, body) -> go body
    | Match(_, e, cases) ->
        go e >> check_cases cases
    | App (_, f, x) -> go f >> go x
    | GetField(_, e, _) -> go e

    | Var _ -> Ok ()
    | Ctor _ -> Ok ()
  in go

let check expr =
  check_unbound_vars expr
  >> check_duplicate_record_fields expr
