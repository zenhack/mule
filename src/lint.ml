open OrErr
open Ast.Surface.Expr
module VSet = Set.Make(Ast.Var)
module LSet = Set.Make(Ast.Label)

(* Free variables in an expression *)
let rec free_vars env =
  function
  | Var v ->
      if VSet.mem v env then
        VSet.empty
      else
        VSet.singleton v
  | Lam ((pat :: pats), body) ->
      case_free_vars env (pat, (Lam (pats, body)))
  | Lam ([], body) ->
      free_vars env body
  | App (f, x) ->
      VSet.union (free_vars env f) (free_vars env x)
  | Record fields -> fields_free_vars env fields
  | Update(e, fields) ->
      VSet.union
        (free_vars env e)
        (fields_free_vars env fields)
  | GetField(e, _) ->
      free_vars env e
  | Ctor _ ->
      VSet.empty
  | Match (e, cases) ->
      List.fold_left
        VSet.union
        (free_vars env e)
        (List.map (case_free_vars env) cases)
  | Let (pat, e, body) ->
      VSet.union
        (case_free_vars env (pat, e))
        (case_free_vars env (pat, body))
and case_free_vars env (p, body) =
  match p with
    | Ast.Surface.Pattern.Wild ->
        free_vars env body
    | Ast.Surface.Pattern.Var v ->
        free_vars (VSet.add v env) body
    | Ast.Surface.Pattern.Ctor (_, p') ->
        case_free_vars env (p', body)
    | Ast.Surface.Pattern.Annotated (p', _) ->
        case_free_vars env (p', body)
and fields_free_vars env fields =
  fields
    |> List.map (fun (_, v) -> free_vars env v)
    |> List.fold_left VSet.union VSet.empty

(* Check for unbound variables. *)
let check_unbound_vars expr =
  let free = free_vars VSet.empty expr in
  match VSet.find_first_opt (fun _ -> true) free with
  | Some x -> Err (Error.UnboundVar x)
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
    | Record fields ->
        check_fields LSet.empty LSet.empty fields
    | Update(e, fields) ->
        go e
        >> check_fields LSet.empty LSet.empty fields

    (* The rest of this is just walking down the tree *)
    | Lam (_, body) -> go body
    | Match(e, cases) ->
        go e >> check_cases cases
    | App (f, x) -> go f >> go x
    | GetField(e, _) -> go e
    | Let (_, e, body) -> go e >> go body

    | Var _ -> Ok ()
    | Ctor _ -> Ok ()
  in go

let check expr =
  check_unbound_vars expr
  >> check_duplicate_record_fields expr
