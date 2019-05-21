open Typecheck_types
open Ast
open Ast.Desugared

let ivar i = Ast.Var.of_string ("t" ^ Int.to_string i)

let maybe_add_rec i vars ty =
  let myvar = ivar i in
  if Set.mem vars myvar then
    ( Set.remove vars myvar
    , Type.Recur(i, myvar, ty)
    )
  else
    (vars, ty)

let rec add_rec_binders ty =
  match ty with
  | Type.Named _ ->
      ( VarSet.empty
      , ty
      )
  | Type.Var (_, v) ->
      ( VarSet.singleton v
      , ty
      )
  | Type.Recur(i, v, t) ->
      let (vs, ts) = add_rec_binders t in
      ( Set.remove vs (ivar i)
      , Type.Recur(i, v, ts)
      )
  | Type.Fn (i, f, x) ->
      let (fv, ft) = add_rec_binders f in
      let (xv, xt) = add_rec_binders x in
      maybe_add_rec i (Set.union fv xv) (Type.Fn(i, ft, xt))
  | Type.Record { r_info; r_types; r_values } ->
      let (ty_vars, ty_ret) = row_add_rec_binders r_types in
      let (val_vars, val_ret) = row_add_rec_binders r_values in
      maybe_add_rec r_info (Set.union ty_vars val_vars) (Type.Record
        { r_info
        ; r_types = ty_ret
        ; r_values = val_ret
        })
  | Type.Union(i, ctors, rest) ->
      let (vars, ret) = row_add_rec_binders (i, ctors, rest) in
      maybe_add_rec i vars (Type.Union ret)
  | Type.Quant(i, q, bound, kind, body) ->
      let (vars, body') = add_rec_binders body in
      maybe_add_rec i vars (Type.Quant(i, q, bound, kind, body'))
and row_add_rec_binders (i, fields, rest) =
  let row_var = match rest with
    | Some v -> VarSet.singleton v
    | None -> VarSet.empty
  in
  let fields_vars =
    List.map fields ~f:(fun (lbl, ty) -> (lbl, add_rec_binders ty))
  in
  let vars = List.fold_left fields_vars
    ~init:row_var
    ~f:(fun accum (_, (vars, _)) -> Set.union accum vars)
  in
  let fields' = List.map fields_vars ~f:(fun (lbl, (_, ty)) -> (lbl, ty)) in
  (vars, (i, fields', rest))
let add_rec_binders ty =
  snd (add_rec_binders ty)

(* Extract a type from a (solved) unification variable. *)
let rec get_var_type env t =
  let i = (get_tyvar t).ty_id in
  match t with
  | _ when Set.mem env (ivar i) ->
      Type.Var (i, (ivar i))
  | `Quant (_, arg) ->
      (* TODO: it would be good to actually show the quantifiers. *)
      get_var_type env (UnionFind.get arg)
  | `Free ({ty_id = i; _}, _) -> Type.Var (i, (ivar i))
  | `Const({ty_id = i; _}, c, args, _) ->
      let env' = Set.add env (ivar i) in
      begin match c, args with
      | `Named "->", [param, _; ret, _] ->
          Type.Fn
            ( i
            , get_var_type env' (UnionFind.get param)
            , get_var_type env' (UnionFind.get ret)
            )
      | `Named "{...}", [r_types, _; r_values, _] ->
          let (types_fields, types_rest) =
            get_var_row env' (UnionFind.get r_types)
          in
          let (values_fields, values_rest) =
            get_var_row env' (UnionFind.get r_values)
          in
          Type.Record
            { r_info = i
            ; r_types = (Gensym.gensym (), types_fields, types_rest)
            ; r_values = (Gensym.gensym (), values_fields, values_rest)
            }
      | `Named "|", [row, _] ->
          let (fields, rest) =
            get_var_row env' (UnionFind.get row)
          in
          Type.Union(i, fields, rest)
      | `Named s, _ ->
          Type.Named(i, s)
      | `Extend _, _ ->
          failwith "BUG: Kind error"
      end
and get_var_row env r =
  let i = (get_tyvar r).ty_id in
  let (fields, rest) =
    match r with
    | _ when Set.mem env (ivar i) -> ([], Some (ivar i))
    | `Quant(_, arg) ->
        get_var_row env (UnionFind.get arg)
    | `Free ({ty_id = i; _}, _) -> ([], Some (ivar i))
    | `Const({ty_id = i; _}, c, args, _) ->
        begin match c, args with
        | `Named "<empty>", [] -> ([], None)
        | `Extend lbl, [ty, _; rest, _] ->
            let env' = Set.add env (ivar i) in
            let (fields, rest) = get_var_row env' (UnionFind.get rest) in
            ( ( lbl
              , get_var_type env' (UnionFind.get ty)
              )
              :: fields
            , rest
            )
        | `Named "<empty>", _ | `Extend _, _ ->
            failwith "BUG: wrong number of args"
        | `Named _, _ ->
            failwith "BUG: not a row"
        end
  in

  (* Filter out duplicate field names: *)
  let seen = ref LabelSet.empty in
  let fields = List.filter fields ~f:(fun (l, _) ->
    if Set.mem !seen l then
      false
    else
      (seen := Set.add !seen l; true)
  )
  in

  (* Ensure a consistent ordering: *)
  ( List.sort fields ~compare:(fun (ll, _) (lr, _) -> Label.compare ll lr)
  , rest
  )
let get_var_type uvar =
  UnionFind.get uvar
    |> get_var_type VarSet.empty
    |> add_rec_binders
    |> Relabel.relabel_type ()
