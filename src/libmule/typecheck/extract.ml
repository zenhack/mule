open Typecheck_types

module DT = Desugared_ast_type
module DK = Desugared_ast_kind
module ST = Surface_ast.Type

let get_ty_id: u_type -> int = function
  | `Free({ty_id; _}, _) -> ty_id
  | `Const(ty_id, _, _, _) -> ty_id
  | `Quant(ty_id, _, _, _, _) -> ty_id

let var_of_int n =
  Common_ast.Var.of_string ("$$" ^ Int.to_string n)
let mk_var id =
    ( DT.Var {
        v_info = id;
        v_var = var_of_int id;
      }
    , IntSet.singleton id
    )

let rec go seen uv =
  let t = UnionFind.get uv in
  let ty_id = get_ty_id t in
  if Set.mem seen ty_id then
    mk_var ty_id
  else
    begin match t with
      | `Free _ -> mk_var ty_id
      | `Quant(q_id, q, v_id, _, body) ->
          let (body', fvs) = go (Set.add seen q_id) body in
          maybe_add_recur
            q_id
            (Set.remove fvs v_id)
            (DT.Quant {
                q_info = q_id;
                q_quant = q;
                q_var = var_of_int v_id;
                q_body = body';
            })
      | `Const(ty_id, `Named `Record, [rtypes, _; rvals, _], _) ->
          let seen' = Set.add seen ty_id in
          let (r_types, fv_types) = go_row seen' rtypes in
          let (r_values, fv_values) = go_row seen' rvals in
          DT.Record {
            r_info = ty_id;
            r_types;
            r_values;
            r_src = ST.Record {r_items = []};
          }
          |> maybe_add_recur ty_id (Set.union fv_types fv_values)
      | `Const(ty_id, `Named `Union, [row, _], _) ->
          let seen' = Set.add seen ty_id in
          let (r, fvs) = go_row seen' row in
          DT.Union{u_row = r}
          |> maybe_add_recur ty_id fvs
      | `Const(ty_id, c, args, _) ->
          let seen' = Set.add seen ty_id in
          let args_fvs =
            List.map args ~f:(fun (t, _) -> go seen' t)
          in
          let args = List.map args_fvs ~f:fst in
          let fvs =
            List.map args_fvs ~f:snd
            |> Set.union_list (module Int)
          in
          maybe_add_recur ty_id fvs (make_const_type ty_id c args)
    end
and go_row seen uv =
  let r = UnionFind.get uv in
  let ty_id = get_ty_id r in
  match r with
    | `Free _ ->
        ( (ty_id, [], Some (var_of_int ty_id))
        , IntSet.singleton ty_id
        )
    | `Const(_, `Named `Empty, _, _) ->
        ((ty_id, [], None), IntSet.empty)
    | `Const(_, `Extend lbl, [h, _; t, _], _) ->
        let (h', hfv) = go seen h in
        let ((_, fields, tail), tfv) = go_row seen t in
        ( (ty_id, ((lbl, h') :: fields), tail)
        , Set.union hfv tfv
        )
    | _ ->
        MuleErr.bug "Invalid row"
and maybe_add_recur id fvs ty =
  if Set.mem fvs id then
    ( DT.Recur {
        mu_info = id;
        mu_var = var_of_int id;
        mu_body = ty;
      }
    , Set.remove fvs id
    )
  else
    (ty, fvs)
and make_const_type id c args =
  match c, args with
  | `Named name, [] -> DT.Named {
      n_info = id;
      n_name = name;
    }
  | `Named `Fn, [p; r] -> DT.Fn {
      fn_info = id;
      fn_pvar = None;
      fn_param = p;
      fn_ret = r;
    }
  | `Named `Apply, [f; x] -> DT.App {
      app_info = id;
      app_fn = f;
      app_arg = x;
    }
  | `Named `Lambda, [p; body] ->
      begin match p with
      | DT.Var{v_var; _} ->
          DT.TypeLam {
            tl_info = id;
            tl_param = v_var;
            tl_body = body;
          }
      | _ ->
          MuleErr.bug "type lambda has non-variable as a parameter"
      end
  | `Named name, _ ->
      failwith ("TODO: make_const_type " ^ string_of_typeconst_name name)
  | `Extend _, _ ->
      MuleErr.bug "kind mismatch"

let get_var_type uv =
  fst (go IntSet.empty uv)
  |> Relabel.relabel_type ()

let get_var_row uv =
  fst (go_row (IntSet.empty) uv)

let rec kind: u_kind -> DK.maybe_kind = function
  | `Free _ -> `Unknown
  | `Type -> `Type
  | `Row -> `Row
  | `Arrow(x, y) ->
      `Arrow(kind (UnionFind.get x), kind (UnionFind.get y))
