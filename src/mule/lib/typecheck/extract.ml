open Typecheck_types

module DT = Desugared_ast_type
module DK = Desugared_ast_kind
module ST = Surface_ast.Type

let var_of_int n =
  Common_ast.Var.of_string ("$$" ^ Int.to_string n)
let mk_var id =
  ( DT.Var {
        v_info = id;
        v_var = var_of_int id;
        v_src = `Generated;
      }
  , IntSet.singleton id
  )

let rec go seen uv =
  let t = UnionFind.get uv in
  let ty_id = get_id t in
  if Set.mem seen ty_id then
    mk_var ty_id
  else
    begin match t with
      | `Free _ | `Bound _ -> mk_var ty_id
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
            r_src = None;
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
  let ty_id = get_id r in
  match r with
  | `Const(_, `Extend lbl, [h, _; t, _], _) ->
      let (h', hfv) = go seen h in
      let (DT.{row_fields; row_rest; _}, tfv) = go_row seen t in
      ( DT.{
            row_info = ty_id;
            row_fields = ((lbl, h') :: row_fields);
            row_rest;
          }
      , Set.union hfv tfv
      )
  | _ ->
      let (tail, ftv) = go seen uv in
      ( DT.{
            row_info = ty_id;
            row_fields = [];
            row_rest = Some tail;
          }
      , ftv
      )
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

(* Strip any quantifiers out of the type aren't needed. This takes two forms:
 *
 * - things like `all a. int`, where you have a quantified value that isn't
 *   actually used.
 * - Things with row types like:
 *   - `Foo int | ...all r. r`, which is the same as just `Foo int`.
 *   - `{...exist r. r}` which is the same as just `{}`.
*)
let strip_needless_quantifiers ty =
  let rec go ty = match ty with
    (* These two cases may shadow a variable in the body, in which
     * case we have to remove it from the free variables. Either
     * way, we keep the type structure as-is (after recursing): *)
    | DT.Fn{fn_pvar; fn_param; fn_ret; fn_info} ->
        let fn_param, fv_param = go fn_param in
        let fn_ret, fv_ret = go fn_ret in
        let fv =
          begin match fn_pvar with
            | None -> Set.union fv_param fv_ret
            | Some v -> Set.union fv_param (Set.remove fv_ret v)
          end
        in
        (DT.Fn{fn_pvar; fn_param; fn_ret; fn_info}, fv)
    | DT.TypeLam{tl_info; tl_param; tl_body} ->
        let tl_body, fv_body = go tl_body in
        ( DT.TypeLam {tl_info; tl_param; tl_body}
        , Set.remove fv_body tl_param
        )

    (* If the body contains the bound variable, keep things as is,
     * otherwise drop the binder: *)
    | DT.Recur {mu_var; mu_body; mu_info} ->
        let mu_body, fvs = go mu_body in
        if Set.mem fvs mu_var then
          ( DT.Recur{mu_var; mu_info; mu_body}
          , Set.remove fvs mu_var
          )
        else
          (mu_body, fvs)
    | DT.Quant{q_info; q_quant; q_var; q_body} ->
        let q_body, fvs = go q_body in
        if Set.mem fvs q_var then
          ( DT.Quant{q_info; q_quant; q_var; q_body}
          , Set.remove fvs q_var
          )
        else
          (q_body, fvs)

    (* Leaves of the tree. *)
    | DT.Var{v_var; _} -> (ty, VarSet.singleton v_var)
    | DT.Path{p_var = `Var v; _} -> (ty, VarSet.singleton v)
    | DT.Path{p_var = `Import _; _} | DT.Named _ | DT.Opaque _ ->
        (ty, VarSet.empty)

    (* These we just apply recursivley; no special logic for them. *)
    | DT.Record{r_info; r_types; r_values; r_src} ->
        let r_types, fv_types = go_row r_types (`Record `Type) in
        let r_values, fv_values = go_row r_values (`Record `Value) in
        ( DT.Record{r_info; r_types; r_values; r_src}
        , Set.union fv_types fv_values
        )
    | DT.Union{u_row} ->
        let u_row, fvs = go_row u_row `Union in
        (DT.Union{u_row}, fvs)
    | DT.App{app_info; app_fn; app_arg} ->
        let app_fn, fv_fn = go app_fn in
        let app_arg, fv_arg = go app_arg in
        ( DT.App{app_info; app_fn; app_arg}
        , Set.union fv_fn fv_arg
        )
  and go_row {row_info; row_fields; row_rest} parent =
    let row_fields, fv_fields =
      List.fold_right
        row_fields
        ~init:([], VarSet.empty)
        ~f:(fun (l, t) (fs, fvs) ->
          let t, fv_t = go t in
          ( ((l, t) :: fs)
          , (Set.union fvs fv_t)
          )
        )
    in
    let row_rest, fvs = match row_rest with
      | None -> (None, fv_fields)
      | Some rest ->
          match rest with
          | DT.Quant{q_var; q_quant; q_body = DT.Var{v_var; _}; _}
            when Common_ast.Var.equal q_var v_var ->
              begin match q_quant, parent with
                | `All, `Union
                | `All, `Record `Type
                | `Exist, `Record `Value ->
                    (None, fv_fields)
                | _ ->
                    let (rest, fv) = go rest in
                    (Some rest, fv)
              end
          | _ ->
              let (rest, fv) = go rest in
              (Some rest, fv)
    in
    ({row_info; row_fields; row_rest}, fvs)
  in
  fst (go ty)

let get_var_type uv =
  fst (go IntSet.empty uv)
  |> strip_needless_quantifiers
  |> Relabel.relabel_type ()

let get_var_row uv =
  fst (go_row (IntSet.empty) uv)

let rec kind: u_kind -> DK.maybe_kind = function
  | `Free _ -> `Unknown
  | `Type -> `Type
  | `Row -> `Row
  | `Arrow(x, y) ->
      `Arrow(kind (UnionFind.get x), kind (UnionFind.get y))
