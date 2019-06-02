open Ast.Surface
open Ast.Surface.Expr

let rec collect_pat_vars = function
  | Pattern.Integer _ -> VarSet.empty
  | Pattern.Wild -> VarSet.empty
  | Pattern.Var v -> VarSet.singleton v
  | Pattern.Ctor(_, p) -> collect_pat_vars p
  | Pattern.Annotated(p, _) -> collect_pat_vars p

let err e =
  raise (MuleErr.MuleExn e)
let unboundVar v =
  err (MuleErr.UnboundVar v)
let duplicate_fields dups =
  err (MuleErr.DuplicateFields dups)

(* Check for unbound variables. *)
let check_unbound_vars expr =
  let rec go_expr typ term = function
    | Integer _ -> ()
    | Var v when Set.mem term v -> ()
    | Var v -> unboundVar v
    | Lam([], body) ->
      go_expr typ term body
    | Lam(pat :: pats, body) ->
      go_pat typ pat;
      let term_new = collect_pat_vars pat in
      go_expr typ (Set.union term term_new) (Lam(pats, body))
    | App(f, x) -> go_expr typ term f; go_expr typ term x
    | Record fields ->
      let new_vars =
        List.filter_map fields ~f:(function
            | `Value(l, _, _) ->
              Some (Ast.Var.of_string (Ast.Label.to_string l))
            | _ ->
              None
          )
        |> Set.of_list (module Ast.Var)
      in
      List.iter fields ~f:(go_field typ (Set.union term new_vars))
    | GetField (e, _) -> go_expr typ term e
    | Ctor _ -> ()
    | Update (e, fields) ->
      go_expr typ term e;
      List.iter fields ~f:(go_field typ term)
    | Match (e, cases) ->
      go_expr typ term e;
      List.iter cases ~f:(go_case typ term)
    | Let (pat, e, body) ->
      let term_new = Set.union term (collect_pat_vars pat) in
      go_pat typ pat;
      go_expr typ term_new e;
      go_expr typ term_new body
    | WithType (e, ty) ->
      go_expr typ term e;
      go_type typ ty
  and go_field typ term = function
    | `Value (_, ty, e) ->
      go_expr typ term e;
      Option.iter ty ~f:(go_type typ)
    | `Type (_, ty) ->
      go_type typ ty
  and go_case typ term (pat, e) =
    go_pat typ pat;
    let pat_new = collect_pat_vars pat in
    go_expr typ (Set.union term pat_new) e
  and go_pat typ = function
    | Pattern.Integer _ -> ()
    | Pattern.Wild -> ()
    | Pattern.Var _ -> ()
    | Pattern.Ctor(_, p) -> go_pat typ p
    | Pattern.Annotated(_, ty) -> go_type typ ty
  and go_type typ = function
    | Type.Var v | Type.Path(v, _) when Set.mem typ v -> ()
    | Type.Var v | Type.Path(v, _) -> unboundVar v
    | Type.Quant(_, vars, ty) ->
      go_type (List.fold ~init:typ ~f:Set.add vars) ty
    | Type.Recur(var, ty) ->
      go_type (Set.add typ var) ty
    | Type.Fn(param, ret) ->
      go_type typ param;
      go_type typ ret
    | Type.Record (Type.Type(_, Some ty) :: rest) ->
      go_type typ ty;
      go_type typ (Type.Record rest)
    | Type.Record (Type.Type(_, None) :: rest) ->
      go_type typ (Type.Record rest)
    | Type.Record (Type.Field(_, ty) :: rest) ->
      go_type typ ty;
      go_type typ (Type.Record rest)
    | Type.Record (Type.Rest var :: rest) ->
      go_type typ (Type.Var var);
      go_type typ (Type.Record rest)
    | Type.Record [] -> ()
    | Type.Ctor _ -> ()
    | Type.App (f, x) ->
      go_type typ f;
      go_type typ x
    | Type.Union(x, y) ->
      go_type typ x;
      go_type typ y
    | Type.RowRest v ->
      go_type typ (Type.Var v)
    | Type.Annotated(v, ty) ->
      go_type (Set.add typ v) ty
  in
  let term =
    Intrinsics.intrinsics
    |> Map.keys
    |> Set.of_list (module Ast.Var)
  in
  go_expr VarSet.empty term expr

(* Check for duplicate record fields (in both expressions and types) *)
let check_duplicate_record_fields =
  let rec go_expr = function
    | Integer _ -> ()
    | Record fields ->
      go_fields fields
    | Update(e, fields) ->
      go_expr e; go_fields fields

    | Lam (pats, body) ->
      List.iter pats ~f:go_pat;
      go_expr body
    | Match(e, cases) ->
      go_expr e;
      List.iter cases ~f:go_case
    | App (f, x) -> go_expr f; go_expr x
    | GetField(e, _) -> go_expr e
    | Let (pat, e, body) ->
      go_pat pat;
      go_expr e;
      go_expr body
    | Var _ -> ()
    | Ctor _ -> ()
    | WithType(e, ty) ->
      go_expr e;
      go_type ty
  and go_fields fields =
    List.iter fields ~f:(function
        | `Value (_, ty, e) ->
          Option.iter ty ~f:go_type;
          go_expr e
        | `Type (_, ty) ->
          go_type ty
      );
    let labels = List.map fields ~f:(function
        | `Value (lbl, _, _) -> lbl
        | `Type (lbl, _) -> lbl
      ) in
    go_labels labels
  and go_pat = function
    | Pattern.Integer _ -> ()
    | Pattern.Annotated(pat, ty) -> go_pat pat; go_type ty
    | Pattern.Ctor(_, pat) -> go_pat pat
    | Pattern.Var _ | Pattern.Wild -> ()
  and go_type = function
    | Type.Var _
    | Type.Path _
    | Type.Ctor _
    | Type.RowRest _ -> ()
    | Type.Quant(_, _, ty) -> go_type ty
    | Type.Recur(_, ty) -> go_type ty
    | Type.Fn(param, ret) -> go_type param; go_type ret
    | Type.Record fields ->
      List.map fields ~f:(function
          | Type.Rest _ -> []
          | Type.Field(lbl, ty)
          | Type.Type(lbl, Some ty) ->
            go_type ty;
            [lbl]
          | Type.Type (lbl, None) ->
            [lbl]
        )
      |> List.concat
      |> go_labels
    | Type.Union(l, r) -> go_type l; go_type r
    | Type.App(f, x) -> go_type f; go_type x
    | Type.Annotated(_, ty) -> go_type ty
  and go_labels =
    let rec go all dups = function
      | (l :: ls) when Set.mem all l ->
        go all (Set.add dups l) ls
      | (l :: ls) ->
        go (Set.add all l) dups ls
      | [] when Set.is_empty dups -> ()
      | [] -> duplicate_fields (Set.to_list dups)
    in go LabelSet.empty LabelSet.empty
  and go_case (pat, body) =
    go_pat pat;
    go_expr body
  in
  go_expr

let check expr =
  try
    begin
      check_unbound_vars expr;
      check_duplicate_record_fields expr;
      Ok ()
    end
  with
    MuleErr.MuleExn e -> Error e
