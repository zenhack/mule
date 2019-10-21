open Typecheck_types

module DE = Desugared_ast_expr
module DT = Desugared_ast_type
module C = Common_ast.Const
module Label = Common_ast.Label

type context = {
  type_env : u_var VarMap.t;
  vals_env : u_var VarMap.t;
  locals : (int * u_var) list ref;
}

let unbound_var v =
  MuleErr.throw (`UnboundVar v)

let apply_kids: u_type -> f:(u_var -> u_var) -> u_type =
  fun  t ~f -> match t with
    | `Free _ -> t
    | `Quant(q_id, q, v, k, body) -> `Quant(q_id, q, v, k, f body)
    | `Const(c_id, c, args, k) ->
        `Const(c_id, c, List.map args ~f:(fun (t, k) -> (f t, k)), k)

let rec subst ~target ~replacement uv =
  match UnionFind.get uv with
    | `Free({ty_id; _}, _) when ty_id = target -> replacement
    | `Free _ -> uv
    | u -> UnionFind.make (copy (apply_kids u ~f:(subst ~target ~replacement)))
and copy = function
  | `Free _ -> MuleErr.bug "impossible"
  | `Const(_, c, args, k) -> `Const(Gensym.gensym (), c, args, k)
  | `Quant(_, q, v, k, body) ->
      let qid = Gensym.gensym () in
      let v' = Gensym.gensym () in
      `Quant(qid, q, v', k, subst body ~target:v ~replacement:(UnionFind.make (`Free
            ( {ty_flag = `Explicit; ty_id = v'}
            , k
            ))))

let wrong_num_args ctor want gotl gotr =
  MuleErr.bug
    (String.concat [
          "Wrong number of arguments for ";
          ctor ^ " type constructor: ";
          " wanted ";
          Int.to_string want;
          " but got (";
          Int.to_string (List.length gotl);
          ", ";
          Int.to_string (List.length gotr);
          ").";
        ])

(* Run f with an empty locals stack. When it returns, the result will be quantified over
 * any locals created that remain un-substituted. *)
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
          Some (fun acc -> UnionFind.make (`Quant(Gensym.gensym (), q, ty_id, k, acc)))
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

let synth_const: C.t -> u_var = function
  | C.Integer _ -> int
  | C.Text _ -> text
  | C.Char _ -> char

let find_bound env var = match Map.find env var with
  | Some value -> value
  | None -> unbound_var var


(* Build an initial context, which contains types for the stuff in intrinsics. *)
let rec make_initial_context () =
  let dummy = {
    type_env = VarMap.empty;
    vals_env = VarMap.empty;
    locals = ref [];
  }
  in
  let type_env =
    Map.map Intrinsics.types ~f:(make_type dummy)
  in
  let vals_env =
    Map.map Intrinsics.values ~f:(fun (ty, _) ->
      make_type { dummy with type_env = type_env } ty
    )
  in
  { type_env; vals_env; locals = ref [] }

(* Turn a type in the AST into a type in the type checker: *)
and make_type ctx ty = match ty with
  | DT.Var {v_var; _} ->
      find_bound ctx.type_env v_var
  | DT.Quant {q_quant; q_var; q_body; _} ->
      quant q_quant (gen_k ()) (fun v ->
        make_type
          { ctx with type_env = Map.set ctx.type_env ~key:q_var ~data:v }
          q_body
      )
  | DT.Opaque _ ->
      MuleErr.bug "Opaques should have been qualified before typechecking."
  | DT.Named{n_name; _} ->
      const_ty n_name
  | DT.Record{r_types; r_values; _} ->
      record (make_row ctx r_types) (make_row ctx r_values)
  | DT.Fn{fn_param; fn_ret; fn_pvar = None; _} ->
      make_type ctx fn_param **> make_type ctx fn_ret
  | DT.Union{u_row} ->
      union (make_row ctx u_row)
  | _ -> failwith ("TODO make_type: " ^ Pretty.typ ty)
and make_row ctx (_, fields, v) =
  let tail = match v with
    | None -> empty
    | Some v -> find_bound ctx.type_env v
  in
  List.fold_right fields ~init:tail ~f:(fun (lbl, ty) rest ->
    extend lbl (make_type ctx ty) rest
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
          let r =
            synth
              { ctx with vals_env = Map.set ctx.vals_env ~key:l_param ~data:p }
              l_body
          in
          p **> r
        )
    | DE.GetField{gf_lbl} ->
        all krow (fun rv -> all ktype (fun a -> all krow (fun rt ->
            record rt (extend gf_lbl a rv) **> a
          )))
    | DE.UpdateVal {uv_lbl} ->
        all krow (fun rv -> (all krow (fun rt -> all ktype (fun t ->
            record rt rv **> t **> record rt (extend uv_lbl t rv)
          ))))
    | DE.UpdateType {ut_lbl; ut_type; ut_record} ->
        with_locals ctx (fun ctx ->
          let rv = fresh_local ctx `Flex krow in
          let rt = fresh_local ctx `Flex krow in
          let _ = check ctx ut_record (record rt rv) in
          record (extend ut_lbl (make_type ctx ut_type) rt) rv
        )
    | DE.EmptyRecord ->
        all krow (fun rtypes -> record rtypes empty)
    | DE.Ctor{c_lbl; c_arg} ->
        let arg_t = synth ctx c_arg in
        all krow (fun r -> union (extend c_lbl arg_t r))
    | DE.WithType {wt_expr; wt_type} ->
        check ctx wt_expr (make_type ctx wt_type)
    | DE.Let{let_v; let_e; let_body} ->
        let ty = synth ctx let_e in
        synth
            { ctx
              with vals_env = Map.set ctx.vals_env ~key:let_v ~data:ty
            }
            let_body
    | DE.App{app_fn; app_arg} ->
        with_locals ctx (fun ctx ->
          let p = fresh_local ctx `Flex ktype in
          let r = fresh_local ctx `Flex ktype in
          let _ = check ctx app_fn (p **> r) in
          let _ = check ctx app_arg p in
          r
        )
    | DE.ConstMatch {cm_cases; cm_default} ->
        with_locals ctx (fun ctx ->
          let param = fresh_local ctx `Flex ktype in
          let result = fresh_local ctx `Flex ktype in
          let ftype = check ctx cm_default (param **> result) in
          begin match Map.to_alist cm_cases with
          | [] -> ftype
          | cs ->
              List.iter cs ~f:(fun (p, body) ->
                let _ = check_const ctx p param in
                let _ = check ctx body result in
                ()
              );
              ftype
          end
        )
    | DE.Match {cases; default} ->
        with_locals ctx (fun ctx ->
          let map = Map.map cases ~f:(fun _ -> fresh_local ctx `Flex ktype) in
          let param_row =
            Map.fold map
              ~init:begin match default with
                | None -> empty
                | Some _ -> fresh_local ctx `Flex krow
              end
              ~f:(fun ~key ~data r -> extend key data r)
          in
          let param = union param_row in
          let result = match default with
            | None -> fresh_local ctx `Flex ktype
            | Some (None, body) ->
                synth ctx body
            | Some (Some v, body) ->
                synth
                  { ctx with vals_env = Map.set ctx.vals_env ~key:v ~data:param }
                  body
          in
          Map.iteri map ~f:(fun ~key ~data ->
            let (v, body) = Util.find_exn cases key in
            let _ = check
              { ctx with vals_env = Map.set ctx.vals_env ~key:v ~data }
              body
              result
            in
            ()
          );
          (param **> result)
        )
    | _ -> failwith "TODO: synth"
and check: context -> 'i DE.t -> u_var -> u_var =
  fun ctx e ty_want ->
    let ty_got = synth ctx e in
    require_subtype ctx ~sub:ty_got ~super:ty_want;
    ty_want
and require_subtype: context -> sub:u_var -> super:u_var -> unit =
  fun ctx ~sub ~super ->
    trace_req_subtype ~sub ~super;
    begin match UnionFind.get sub, UnionFind.get super with
      | _ when UnionFind.equal sub super -> ()
      (* The UnionFind variables are different, but the IDs are the same. I(isd) am not
       * sure this can actually come up, but if it does, this is the behavior that
       * makes sense. *)
      | l, r when get_id l = get_id r -> UnionFind.merge (fun _ r -> r) sub super

      | `Free({ty_flag = `Rigid; ty_id = l_id}, _), `Free({ty_flag = `Rigid; ty_id = r_id}, _)
          when l_id = r_id ->
            UnionFind.merge (fun _ r -> r) sub super
      | `Free({ty_flag = `Flex; ty_id = l_id}, kl), `Free({ty_flag = `Flex; ty_id = r_id }, kr) ->
          (* Both sides are flexible variables; merge them, using the larger of their
           * scopes.
           *
           * FIXME: the "reason" here is totally bogus; do something better. *)
          UnionFind.merge (Infer_kind.unify `Frontier) kl kr;
          UnionFind.merge
            (fun _ _ ->
              `Free
                ( {
                    ty_flag = `Flex;
                    (* The variable with the greater scope will have been
                     * created first, and therefore have a smaller id: *)
                    ty_id = Int.min l_id r_id;
                  }
                , kl
                )
            )
            sub super
      (* One side is flexible; set it equal to the other one. *)
      | `Free({ty_flag = `Flex; _}, _), _ -> UnionFind.merge (fun _ r -> r) sub super
      | _, `Free({ty_flag = `Flex; _}, _) -> UnionFind.merge (fun l _ -> l) sub super

      | `Quant(_, q, id, k, body), _ ->
          require_subtype ctx ~sub:(unroll_quant ctx `Sub q id k body) ~super
      | _, `Quant(_, q, id, k, body) ->
          require_subtype ctx ~sub ~super:(unroll_quant ctx `Super q id k body)

      (* Rigid variable should fail (If they were the same already, they would have been
       * covered above): *)
      | `Free({ty_flag = `Rigid; _}, _), _ | _, `Free({ty_flag = `Rigid; _}, _) ->
          MuleErr.throw
            ( `TypeError
                ( `Frontier
                , `PermissionErr `Graft
                )
            )

      (* Mismatched named constructors are never reconcilable: *)
      | `Const(_, `Named n, _, _), `Const(_, `Named m, _, _) when not (String.equal n m) ->
            MuleErr.throw
              (`TypeError
                ( `Frontier
                , `MismatchedCtors(`Named n, `Named m)
                )
              )

      (* All of the zero-argument consts unify with themselves; if the above case
       * didn't cover this one, then we're good: *)
      | `Const(_, `Named _, [], _), `Const(_, `Named _, [], _) -> ()

      (* Functions. *)
      | `Const(_, `Named "->", [psub, _; rsub, _], _),
        `Const(_, `Named "->", [psuper, _; rsuper, _], _) ->
          (* Note the flipped sub vs. super in the parameter case; this is standard
           * contravariance. *)
          require_subtype ctx ~sub:psuper ~super:psub;
          require_subtype ctx ~sub:rsub ~super:rsuper

      | `Const (_, `Named "->", x, _), `Const (_, `Named "->", y, _) ->
          wrong_num_args "->" 2 x y

      | `Const(_, `Named "|", [row_sub, _], _),
        `Const(_, `Named "|", [row_super, _], _) ->
          (* Unions are contravariant in their arguments.
           *
           * TODO: I(isd) _think_ that's right, but I need to think about it a
           * bit more deeply. *)
          require_subtype ctx ~sub:row_super ~super:row_sub

      | `Const(_, `Named "|", x, _), `Const(_, `Named "|", y, _) ->
          wrong_num_args "|" 1 x y

      | `Const(_, `Named "{...}", [rtype_sub, _; rvals_sub, _], _),
        `Const(_, `Named "{...}", [rtype_super, _; rvals_super, _], _) ->
          require_subtype ctx ~sub:rtype_sub ~super:rtype_super;
          require_subtype ctx ~sub:rvals_sub ~super:rvals_super

      | `Const(_, `Named "{...}", x, _), `Const(_, `Named "{...}", y, _) ->
          wrong_num_args "{...}" 2 x y

      | `Const(_, `Named "<empty>", _, _), `Const(_, `Extend l, _, _) ->
          MuleErr.throw
            ( `TypeError
              ( `Frontier
              , `MismatchedCtors(`Named "<empty>", `Extend l)
              )
            )
      | `Const(_, `Extend _, _, _), `Const(_, `Named "<empty>", _, _) ->
          ()
      | `Const(_, `Extend lsub, [hsub, _; tsub, _], _),
        `Const(_, `Extend lsuper, [hsuper, _; tsuper, _], _) ->
          if Label.equal lsub lsuper then
            begin
              require_subtype ctx ~sub:hsub ~super:hsuper;
              require_subtype ctx ~sub:tsub ~super:tsuper
            end
          else
            failwith "TODO: mismatched extend"

      | `Const(_, `Named c, _, _), _ | _, `Const(_, `Named c, _, _) ->
          MuleErr.bug ("Unknown type constructor: " ^ c)

      | _ ->
          MuleErr.bug "TODO: require_subytpe"
    end
and trace_req_subtype ~sub ~super =
  if Config.trace_require_subtype then
    begin
      Caml.print_endline "";
      (Sexp.List [
            Sexp.Atom "require_subtype";
            Sexp.List [
              Sexp.Atom "sub";
              sexp_of_uvar IntSet.empty sub;
            ];
            Sexp.List [
              Sexp.Atom "super";
              sexp_of_uvar IntSet.empty super;
            ];
          ])
      |> Sexp.to_string_hum
      |> Caml.print_endline;
      Caml.print_endline ""
    end
and unroll_quant ctx side q id k body =
  subst
      ~target:id
      ~replacement:(fresh_local ctx (get_flag q side) k)
      body
and check_const ctx c ty_want =
  let ty_got = synth_const c in
  require_subtype ctx ~sub:ty_got ~super:ty_want
