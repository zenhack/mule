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

let rec synth: context -> 'i DE.t -> u_var =
  fun ctx e -> match e with
    | DE.Const {const_val} -> synth_const const_val
    | DE.Embed _ -> text
    | DE.Var {v_var} ->
        begin match Map.find ctx.vals_env v_var with
          | Some v -> v
          | None -> unbound_var v_var
        end
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
            record rt rv **> record rt (extend up_lbl t rv)
          ))))
    | DE.EmptyRecord ->
        exist krow (fun rtypes -> all krow (fun rvals -> record rtypes rvals))
    | DE.Ctor{c_lbl; c_arg} ->
        let arg_t = synth ctx c_arg in
        all krow (fun r -> union (extend c_lbl arg_t r))
