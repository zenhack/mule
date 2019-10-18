open Typecheck_types

module DT = Desugared_ast_type

let get_ty_id: u_type -> int = function
  | `Free({ty_id; _}, _) -> ty_id
  | `Const(ty_id, _, _, _) -> ty_id
  | `Quant(ty_id, _, _, _, _) -> ty_id

let get_var_type uv =
  let var_of_int n =
    Common_ast.Var.of_string ("$$" ^ Int.to_string n)
  in
  let mk_var id =
      ( DT.Var {
          v_info = id;
          v_var = var_of_int id;
        }
      , IntSet.singleton id
      )
  in
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
            maybe_add_recur ty_id fvs (make_const ty_id c args)
      end
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
  and make_const id c args =
    match c, args with
    | `Named name, [] -> DT.Named {
        n_info = id;
        n_name = name;
      }
    | `Named "->", [p; r] -> DT.Fn {
        fn_info = id;
        fn_pvar = None;
        fn_param = p;
        fn_ret = r;
      }
    | `Named "<apply>", [f; x] -> DT.App {
        app_info = id;
        app_fn = f;
        app_arg = x;
      }
    | `Named name, _ ->
        failwith ("TODO: make_const " ^ name)
    | `Extend _, _ ->
        MuleErr.bug "kind mismatch"
  in
  fst (go IntSet.empty uv)
  |> Relabel.relabel_type ()
