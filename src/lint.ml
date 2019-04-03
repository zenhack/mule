open Ast
open Ast.Surface.Expr
open Result.Monad_infix

let (>>) x y = x >>= fun _ -> y

(* Free variables in an expression *)
let rec free_vars env =
  function
  | Var v ->
      if Set.mem env v then
        Set.empty (module Var)
      else
        Set.singleton (module Var) v
  | Lam ((pat :: pats), body) ->
      case_free_vars env (pat, (Lam (pats, body)))
  | Lam ([], body) ->
      free_vars env body
  | App (f, x) ->
      Set.union (free_vars env f) (free_vars env x)
  | Record fields -> fields_free_vars env fields
  | Update(e, fields) ->
      Set.union
        (free_vars env e)
        (fields_free_vars env fields)
  | GetField(e, _) ->
      free_vars env e
  | Ctor _ ->
      Set.empty (module Var)
  | Match (e, cases) ->
      List.fold
        ~f:Set.union
        ~init:(free_vars env e)
        (List.map cases ~f:(case_free_vars env))
  | Let (pat, e, body) ->
      Set.union
        (case_free_vars env (pat, e))
        (case_free_vars env (pat, body))
and case_free_vars env (p, body) =
  match p with
    | Ast.Surface.Pattern.Wild ->
        free_vars env body
    | Ast.Surface.Pattern.Var v ->
        free_vars (Set.add env v) body
    | Ast.Surface.Pattern.Ctor (_, p') ->
        case_free_vars env (p', body)
    | Ast.Surface.Pattern.Annotated (p', _) ->
        case_free_vars env (p', body)
and fields_free_vars env fields =
  fields
    |> List.map ~f:(fun (_, v) -> free_vars env v)
    |> List.fold ~f:Set.union ~init:(Set.empty (module Var))

(* Check for unbound variables. *)
let check_unbound_vars expr =
  let free = free_vars (Set.empty (module Var)) expr in
  match Set.find free ~f:(fun _ -> true) with
  | Some x -> Error (MuleErr.UnboundVar x)
  | None -> Ok ()

(* Check for duplicate record fields *)
let check_duplicate_record_fields =
  let rec go =
    let rec check_fields all dups = function
      | (x, v) :: xs ->
          go v >>
          if Set.mem all x then
            check_fields all (Set.add dups x) xs
          else
            check_fields (Set.add all x) dups xs
      | [] ->
          if Set.is_empty dups then
            Ok ()
          else
            Error
              ( MuleErr.DuplicateFields (Set.to_list dups)
              )
    in
    let rec check_cases = function
      | [] -> Ok ()
      | ((_, body) :: cs) -> go body >> check_cases cs
    in
    function
    | Record fields ->
        check_fields LabelSet.empty LabelSet.empty fields
    | Update(e, fields) ->
        go e
        >> check_fields LabelSet.empty LabelSet.empty fields

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
