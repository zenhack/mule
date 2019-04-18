open Ast.Surface
open Ast.Surface.Expr

let rec collect_pat_vars = function
  | Pattern.Wild -> VarSet.empty
  | Pattern.Var v -> VarSet.singleton v
  | Pattern.Ctor(_, p) -> collect_pat_vars p
  | Pattern.Annotated(p, _) -> collect_pat_vars p

let unboundVar v =
  raise (MuleErr.MuleExn (MuleErr.UnboundVar v))

(* Check for unbound variables. *)
let check_unbound_vars expr =
  let rec go_expr typ term = function
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
        List.iter fields ~f:(go_field typ term)
    | GetField (e, _) -> go_expr typ term e
    | Ctor _ -> ()
    | Update (e, fields) ->
        go_expr typ term e;
        List.iter fields ~f:(go_field typ term)
    | Match (e, cases) ->
        go_expr typ term e;
        List.iter cases ~f:(go_case typ term)
    | Let (pat, e, body) ->
        go_pat typ pat;
        go_expr typ term e;
        let e_new = collect_pat_vars pat in
        go_expr typ (Set.union term e_new) body
  and go_field typ term (_, ty, e) =
    go_expr typ term e;
    Option.iter ty ~f:(go_type typ)
  and go_case typ term (pat, e) =
    go_pat typ pat;
    let pat_new = collect_pat_vars pat in
    go_expr typ (Set.union term pat_new) e
  and go_pat typ = function
    | Pattern.Wild -> ()
    | Pattern.Var _ -> ()
    | Pattern.Ctor(_, p) -> go_pat typ p
    | Pattern.Annotated(_, ty) -> go_type typ ty
  and go_type typ = function
    | Type.Var v when Set.mem typ v -> ()
    | Type.Var v -> unboundVar v
    | Type.Quant(_, vars, ty) ->
        go_type (List.fold ~init:typ ~f:Set.add vars) ty
    | Type.Recur(var, ty) ->
        go_type (Set.add typ var) ty
    | Type.Fn(param, ret) ->
        go_type typ param;
        go_type typ ret
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
  in
  go_expr VarSet.empty VarSet.empty expr

(* Check for duplicate record fields *)
let check_duplicate_record_fields =
  let rec go =
    let rec check_fields all dups = function
      | (x, _, v) :: xs ->
          go v;
          if Set.mem all x then
            check_fields all (Set.add dups x) xs
          else
            check_fields (Set.add all x) dups xs
      | [] when Set.is_empty dups -> ()
      | [] ->
          raise (MuleErr.MuleExn (MuleErr.DuplicateFields (Set.to_list dups)))
    in
    let rec check_cases = function
      | [] -> ()
      | ((_, body) :: cs) -> go body; check_cases cs
    in
    function
    | Record fields ->
        check_fields LabelSet.empty LabelSet.empty fields
    | Update(e, fields) ->
        go e;
        check_fields LabelSet.empty LabelSet.empty fields

    (* The rest of this is just walking down the tree *)
    | Lam (_, body) -> go body
    | Match(e, cases) ->
        go e; check_cases cases
    | App (f, x) -> go f; go x
    | GetField(e, _) -> go e
    | Let (_, e, body) -> go e; go body

    | Var _ -> ()
    | Ctor _ -> ()
  in go

let check expr =
  try
    begin
      check_unbound_vars expr;
      check_duplicate_record_fields expr;
      Ok ()
    end
  with
    MuleErr.MuleExn e -> Error e
