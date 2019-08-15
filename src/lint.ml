open Ast.Surface
open Ast.Surface.Expr

let rec collect_pat_vars = function
  | Pattern.Const _ -> VarSet.empty
  | Pattern.Wild -> VarSet.empty
  | Pattern.Var (v, _) -> VarSet.singleton (Located.value v)
  | Pattern.Ctor(_, p) -> collect_pat_vars (Located.value p)

let err e =
  raise (MuleErr.MuleExn e)
let unboundVar _ v =
  (* TODO: incorporate location info *)
  err (MuleErr.UnboundVar v)
let duplicate_fields dups =
  err (MuleErr.DuplicateFields dups)

(* Check for unbound variables. *)
let check_unbound_vars expr =
  let rec go_expr typ term arg =
    let expr = Located.value arg in
    let loc = Located.loc arg in
    match expr with
    | Const _ -> ()
    | Var v when Set.mem term v -> ()
    | Var v -> unboundVar loc v
    | Lam([], body) ->
        go_expr typ term body
    | Lam(pat :: pats, body) ->
        go_pat typ pat;
        let term_new = collect_pat_vars (Located.value pat) in
        go_expr typ (Set.union term term_new) (Located.at loc (Lam(pats, body)))
    | App(f, x) -> go_expr typ term f; go_expr typ term x
    | Record fields ->
        let (new_types, new_terms) =
          List.partition_map fields ~f:(fun field -> match Located.value field with
              | `Type(l, _, _)  -> `Fst (Ast.var_of_label (Located.value l))
              | `Value(l, _, _) -> `Snd (Ast.var_of_label (Located.value l))
            )
        in
        let typ = List.fold new_types ~init:typ ~f:Set.add in
        let term = List.fold new_terms ~init:term ~f:Set.add in
        List.iter fields ~f:(fun field -> go_field typ term (Located.value field))
    | GetField (e, _) -> go_expr typ term e
    | Ctor _ -> ()
    | Update (e, fields) ->
        go_expr typ term e;
        List.iter fields ~f:(fun field -> go_field typ term (Located.value field))
    | Match (e, cases) ->
        go_expr typ term e;
        List.iter cases ~f:(go_case typ term)
    | Let(binds, body) ->
        go_let typ term binds body
    | WithType (e, ty) ->
        go_expr typ term e;
        go_type typ ty
  and go_let typ term binds body =
    let (typ, term) = List.fold binds ~init:(typ, term) ~f:(fun (typ, term) bind ->
        match Located.value bind with
        | `BindVal(pat, _) -> (typ, Set.union (collect_pat_vars (Located.value pat)) term)
        | `BindType(v, _, _) -> (Set.add typ (Located.value v), term)
      )
    in
    List.iter binds ~f:(go_binding typ term);
    go_expr typ term body
  and go_binding typ term bind = match Located.value bind with
    | `BindVal(pat, body) ->
        go_pat typ pat;
        go_expr typ term body
    | `BindType(_, params, body) ->
        let typ =
          params
          |> List.map ~f:Located.value
          |> List.fold ~init:typ ~f:Set.add
        in
        go_type typ body
  and go_field typ term = function
    | `Value (_, ty, e) ->
        go_expr typ term e;
        Option.iter ty ~f:(go_type typ)
    | `Type (_, params, ty) ->
        let typ =
          List.fold
            params
            ~init:typ
            ~f:(fun acc v -> Set.add acc (Located.value v))
        in
        go_type typ ty
  and go_case typ term lcase =
    let (pat, e) = Located.value lcase in
    go_pat typ pat;
    let pat_new = collect_pat_vars (Located.value pat) in
    go_expr typ (Set.union term pat_new) e
  and go_pat typ p =
    begin match Located.value p with
      | Pattern.Const _ -> ()
      | Pattern.Wild -> ()
      | Pattern.Var (_, None) -> ()
      | Pattern.Var (_, Some ty ) -> go_type typ ty
      | Pattern.Ctor(_, p) -> go_pat typ p
    end
  and go_type typ t = begin match Located.value t with
    | Type.Var v ->
        if not (Set.mem typ v)
        then unboundVar (Located.loc t) v
    | Type.Path(v, _) ->
        if not (Set.mem typ (Located.value v))
        then unboundVar (Located.loc v) (Located.value v)
    | Type.Quant(_, vars, ty) ->
        go_type
          (List.fold
             ~init:typ
             ~f:(fun s v -> Set.add s (Located.value v))
             vars
          )
          ty
    | Type.Recur(var, ty) ->
        go_type (Set.add typ (Located.value var)) ty
    | Type.Fn(param, ret) ->
        begin match Located.value param with
          | Type.Annotated(v, param) ->
              go_type typ param;
              go_type (Set.add typ (Located.value v)) ret
          | _ ->
              go_type typ param;
              go_type typ ret
        end
    | Type.Record record ->
        go_record typ record
    | Type.Ctor _ -> ()
    | Type.App (f, x) ->
        go_type typ f;
        go_type typ x
    | Type.Union(x, y) ->
        go_type typ x;
        go_type typ y
    | Type.RowRest v ->
        go_type typ (Located.at (Located.loc t) (Type.Var v))
    | Type.Annotated(_, ty) ->
        go_type typ ty
  end
  and go_record typ items =
    let (types, values) =
      List.partition_map items ~f:(fun item -> match Located.value item with
          | Type.Type(lbl, _, _) ->
              `Fst
                ( Located.at
                    (Located.loc item)
                    (Ast.var_of_label (Located.value lbl))
                )
          | x ->
              `Snd
                (Located.at
                   (Located.loc item)
                   x
                )
        )
    in
    let typ' =
      List.fold
        types
        ~init:typ
        ~f:(fun s v -> Set.add s (Located.value v))
    in
    List.iter values ~f:(go_record_item typ')
  and go_record_item typ item =
    let loc = Located.loc item in
    begin match Located.value item with
      | Type.Type(_, vars, Some ty) ->
          let typ =
            List.fold vars ~init:typ ~f:(fun s v -> Set.add s (Located.value v))
          in
          go_type typ ty
      | Type.Type(_, _, None) -> ()
      | Type.Field(_, ty) -> go_type typ ty
      | Type.Rest var -> go_type typ (Located.at loc (Type.Var var))
    end
  in
  let keyset m =
    m
    |> Map.keys
    |> Set.of_list (module Ast.Var)
  in
  let term = keyset Intrinsics.values in
  let typ = keyset Intrinsics.types in
  go_expr typ term expr

(* Check for duplicate record fields (in both expressions and types) *)
let check_duplicate_record_fields =
  let rec go_expr ex = match Located.value ex with
    | Const _ -> ()
    | Record fields ->
        go_fields fields
    | Update(e, fields) ->
        go_expr e; go_fields fields
    | Lam (pats, body) ->
        List.iter pats ~f:go_pat;
        go_expr body
    | Match(e, cases) ->
        go_expr e;
        List.iter (List.map cases ~f:Located.value) ~f:go_case
    | App (f, x) -> go_expr f; go_expr x
    | GetField(e, _) -> go_expr e
    | Let(bindings, body) ->
        go_let bindings;
        go_expr body
    | Var _ -> ()
    | Ctor _ -> ()
    | WithType(e, ty) ->
        go_expr e;
        go_type ty
  and go_let =
    List.iter ~f:(fun bind -> match Located.value bind with
        | `BindVal(pat, e) ->
            go_pat pat;
            go_expr e
        | `BindType(_, _, ty) -> go_type ty
      )
  and go_fields fields =
    List.iter fields ~f:(fun field -> match Located.value field with
        | `Value (_, ty, e) ->
            Option.iter ty ~f:go_type;
            go_expr e
        | `Type (_, _, ty) ->
            go_type ty
      );
    let labels = List.map fields ~f:(fun field -> match Located.value field with
        | `Value (lbl, _, _) -> lbl
        | `Type (lbl, _, _) -> lbl
      ) in
    go_labels labels
  and go_pat p = match Located.value p with
    | Pattern.Const _ -> ()
    | Pattern.Ctor(_, pat) -> go_pat pat
    | Pattern.Var (_, None) | Pattern.Wild -> ()
    | Pattern.Var (_, Some ty) -> go_type ty
  and go_type t = match Located.value t with
    | Type.Var _
    | Type.Path _
    | Type.Ctor _
    | Type.RowRest _ -> ()
    | Type.Quant(_, _, ty) -> go_type ty
    | Type.Recur(_, ty) -> go_type ty
    | Type.Fn(param, ret) -> go_type param; go_type ret
    | Type.Record fields ->
        List.map fields ~f:(fun item -> match Located.value item with
            | Type.Rest _ -> []
            | Type.Field(lbl, ty)
            | Type.Type(lbl, _, Some ty) ->
                go_type ty;
                [lbl]
            | Type.Type (lbl, _, None) ->
                [lbl]
          )
        |> List.concat
        |> go_labels
    | Type.Union(l, r) -> go_type l; go_type r
    | Type.App(f, x) -> go_type f; go_type x
    | Type.Annotated(_, ty) -> go_type ty
  and go_labels lbls =
    let rec go all dups = function
      | (l :: ls) when Set.mem all l ->
          go all (Set.add dups l) ls
      | (l :: ls) ->
          go (Set.add all l) dups ls
      | [] when Set.is_empty dups -> ()
      | [] -> duplicate_fields (Set.to_list dups)
    in
    go LabelSet.empty LabelSet.empty (List.map lbls ~f:Located.value)
  and go_case (pat, body) =
    go_pat pat;
    go_expr body
  in
  go_expr

let check expr =
  check_unbound_vars expr;
  check_duplicate_record_fields expr
(* TODO: check for duplicate bound variables (in recursive lets). *)
