open Typecheck_types

module DE = Desugared_ast_expr
module DT = Desugared_ast_type
module C = Common_ast.Const

type context = {
  type_env : u_var VarMap.t;
  vals_env : u_var VarMap.t;
  locals : (int * u_var) list ref;
}

let unbound_var v =
  MuleErr.throw (`UnboundVar v)

let apply_kids t ~f = match t with
  | `Free _ -> t
  | `Quant(q, v, body) -> `Quant(q, v, f body)
  | `Const(c, args, k) ->
      `Const(c, List.map args ~f:(fun (t, k) -> (f t, k)), k)

let copy = function
  | `Free({ty_flag; _}, k) -> `Free({ty_flag; ty_id = Gensym.gensym ()}, k)
  | t -> t

let rec subst ~target ~replacement uv =
  match UnionFind.get uv with
    | `Free({ty_id; _}, _) when ty_id = target -> replacement
    | u -> UnionFind.make (copy (apply_kids u ~f:(subst ~target ~replacement)))

(* Run f with an empty locals stack. When it returns, any locals created that remain
 * un-substituted will be quantified around the result. *)
let with_locals ctx f =
  let new_locals = ref [] in
  let result = f { ctx with locals = new_locals } in
  let remaining = List.filter_map !new_locals ~f:(fun (id, v) -> match UnionFind.get v with
      | `Free({ty_id; ty_flag}, k) when id = ty_id ->
          let q = match ty_flag with
            | `Flex -> `All
            | `Rigid -> `Exist
            | `Explicit -> MuleErr.bug "impossible"
          in
          UnionFind.set (`Free({ty_id; ty_flag = `Explicit}, k)) v;
          Some (fun acc -> UnionFind.make (`Quant(q, ty_id, acc)))
      | _ -> None
    )
  in
  List.fold remaining ~init:result ~f:(fun acc f -> f acc)

(* Create a new local with the given flag and kind. *)
let fresh_local ctx ty_flag k =
  let ty_id = Gensym.gensym () in
  let v = UnionFind.make (`Free({ty_id; ty_flag}, k)) in
  ctx.locals := (ty_id, v) :: !(ctx.locals);
  v

let synth_const = function
  | C.Integer _ -> int
  | C.Text _ -> text
  | C.Char _ -> char

let find_bound env var = match Map.find env var with
  | Some value -> value
  | None -> unbound_var var

let rec make_type ctx ty = match ty with
  | DT.Var {v_var; _} ->
      find_bound ctx.type_env v_var
  | DT.Quant {q_quant; q_var; q_body; _} ->
      quant q_quant (gen_k ()) (fun v ->
        make_type
          { ctx with type_env = Map.set ctx.type_env ~key:q_var ~data:v }
          q_body
      )
and synth: context -> 'i DE.t -> u_var =
  fun ctx e -> match e with
    | DE.Const {const_val} -> synth_const const_val
    | DE.Embed _ -> text
    | DE.Var {v_var} ->
        find_bound ctx.vals_env v_var
    | DE.Lam{l_param; l_body} ->
        with_locals ctx (fun ctx ->
          let p = fresh_local ctx `Flex ktype in
          synth
            { ctx with vals_env = Map.set ctx.vals_env ~key:l_param ~data:p }
            l_body
        )
    | DE.GetField{gf_lbl} ->
        all krow (fun rv -> all ktype (fun a -> all krow (fun rt ->
            record rt (extend gf_lbl a rv) **> a
          )))
    | DE.Update {up_level = `Value; up_lbl} ->
        all krow (fun rv -> (all krow (fun rt -> all ktype (fun t ->
            record rt rv **> t **> record rt (extend up_lbl t rv)
          ))))
    | DE.Update {up_level = `Type; up_lbl} ->
        let k = gen_k () in
        all krow (fun rv -> (all krow (fun rt -> all k (fun t ->
            let tw = witness k t in
            record rt rv **> tw **> record (extend up_lbl tw rt) rv
          ))))
    | DE.EmptyRecord ->
        exist krow (fun rtypes -> all krow (fun rvals -> record rtypes rvals))
    | DE.Ctor{c_lbl; c_arg} ->
        let arg_t = synth ctx c_arg in
        all krow (fun r -> union (extend c_lbl arg_t r))
    | DE.WithType {wt_type} ->
        make_type ctx wt_type **> make_type ctx wt_type
    | DE.Witness {wi_type} ->
        witness (gen_k ()) (make_type ctx wi_type)
and check: context -> 'i DE.t -> u_var -> u_var =
  fun ctx e ty_want ->
    let ty_got = synth ctx e in
    require_subtype ctx ~sub:ty_got ~super:ty_want;
    ty_want
and require_subtype: context -> sub:u_var -> super:u_var -> unit =
  fun ctx ~sub ~super ->
    begin match UnionFind.get sub, UnionFind.get super with
      | _ -> ()
    end
and unroll_quant side q id k body =
  let v = UnionFind.make (`Free({
      ty_id = Gensym.gensym ();
      ty_flag = get_flag q side;
    }, k))
  in
  subst ~target:id ~replacement:v body
