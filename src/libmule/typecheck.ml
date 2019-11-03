open Typecheck_types

module DE = Desugared_ast_expr
module DT = Desugared_ast_type
module C = Common_ast.Const
module Label = Common_ast.Label

type context = {
  type_env : u_var VarMap.t;
  vals_env : u_var VarMap.t;
  locals : (int * u_var) list ref;

  (* [assumptions] is a list of subtyping constraints we've already seen.
   * This is used when checking subtyping constraints that may involve
   * recursive types -- if we are asked to check a subtyping constraint
   * that's already in our assumptions, we just return.
   *
   * Note that from a logician's standpoint this sounds incredibly fishy
   * -- but that's as expected; recursive types amount to circular
   * reasoning.
  *)
  assumptions : IntPairSet.t ref;
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
  (* Nodes we've already seen, to detect cycles and avoid traversing
   * shared sub-graphs. *)
  let seen = ref IntMap.empty in
  let rec go uv =
    begin match UnionFind.get uv with
      | u when get_id u = target -> replacement
      | u when Map.mem !seen (get_id u) -> Util.find_exn !seen (get_id u)
      | `Free _ -> uv
      | `Quant(_, _, v, _, _) when v = target ->
          (* Shadowing the target; stop here. *)
          uv
      | u ->
          (* An an entry to `seen` before traversing, in case we hit
           * ourselves further down. *)
          let result = copy u in
          let result_v = UnionFind.make result in
          seen := Map.set !seen ~key:(get_id u) ~data:result_v;
          UnionFind.set (apply_kids result ~f:go) result_v;
          result_v
    end
  in
  go uv
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
          string_of_typeconst_name ctor ^ " type constructor: ";
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
          let replacement = UnionFind.make (`Free({ty_id; ty_flag = `Explicit}, k)) in
          Some (fun acc ->
            UnionFind.make
              (`Quant(Gensym.gensym (), q, ty_id, k, subst acc
                        ~target:ty_id
                        ~replacement))
          )
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
  let assumptions = ref IntPairSet.empty in
  let dummy = {
    type_env = VarMap.empty;
    vals_env = VarMap.empty;
    locals = ref [];
    assumptions;
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
  { type_env; vals_env; locals = ref []; assumptions; }

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
      with_kind ktype (make_type ctx fn_param) **> with_kind ktype (make_type ctx fn_ret)
  | DT.Fn{fn_param; fn_ret; fn_pvar = Some pvar; _} ->
      with_locals ctx (fun ctx ->
        let param_type = make_type ctx fn_param |> with_kind ktype in
        let param_type = strip_param_exists ctx param_type in
        let ret_type =
          make_type
            { ctx with vals_env = Map.set ctx.vals_env ~key:pvar ~data:param_type }
            fn_ret
          |> with_kind ktype
        in
        param_type **> ret_type
      )
  | DT.Union{u_row} ->
      union (make_row ctx u_row)
  | DT.Recur{mu_var; mu_body; _} ->
      let t = recur (fun v ->
          make_type
            { ctx with type_env = Map.set ctx.type_env ~key:mu_var ~data:v }
            mu_body
        )
      in
      require_kind (get_kind t) ktype;
      t
  | DT.TypeLam{tl_param; tl_body; _} ->
      lambda (gen_k ()) (fun p ->
        make_type
          { ctx with type_env = Map.set ctx.type_env ~key:tl_param ~data:p }
          tl_body
      )
  | DT.App{app_fn; app_arg; _} ->
      let arg = make_type ctx app_arg in
      let k_arg = get_kind arg in
      apply
        (make_type ctx app_fn
         |> with_kind (UnionFind.make(`Arrow(k_arg, gen_k ())))
        )
        arg
  | DT.Path{p_var; p_lbls; _} ->
      let var_type = match Map.find ctx.vals_env p_var with
        | Some ty -> ty |> with_kind ktype
        | None -> unbound_var p_var
      in
      let result_type = fresh_local ctx `Flex (gen_k ()) in
      let path_type = make_path_type result_type p_lbls in
      require_subtype ctx ~sub:var_type ~super:path_type;
      result_type
and make_path_type result_type lbls =
  begin match List.rev lbls with
    | [] ->
        (* Shouldn't happen, but this is correct if it did. *)
        result_type
    | (last :: rest) ->
        List.fold_left
          rest
          ~init:(exist krow (fun rv -> (exist krow (fun rt ->
              record (extend last result_type rt) rv
            ))))
          ~f:(fun tail next ->
            exist krow (fun rv -> (exist krow (fun rt ->
                record
                  rt
                  (extend next tail rv)
              ))))
  end
and strip_param_exists ctx pty =
  match UnionFind.get pty with
  | `Quant(_, `Exist, id, k, body) ->
      strip_param_exists ctx (
        subst
          body
          ~target:id
          ~replacement:(fresh_local ctx `Flex k)
      )
  | _ ->
      pty
and make_row ctx {row_fields; row_rest; _} =
  let tail = match row_rest with
    | None -> empty
    | Some v -> with_kind krow (find_bound ctx.type_env v)
  in
  List.fold_right row_fields ~init:tail ~f:(fun (lbl, ty) rest ->
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
        record (all krow (fun r -> r)) empty
    | DE.Ctor{c_lbl; c_arg} ->
        let arg_t = synth ctx c_arg in
        union (extend c_lbl arg_t (all krow (fun r -> r)))
    | DE.WithType {wt_expr; wt_type} ->
        let want_ty = make_type ctx wt_type |> with_kind ktype in
        let _ = check ctx wt_expr want_ty in
        want_ty
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
    | DE.Match (DE.BConst {cm_cases; cm_default}) ->
        with_locals ctx (fun ctx ->
          let param = fresh_local ctx `Flex ktype in
          let result = fresh_local ctx `Flex ktype in
          let ftype = param **> result in
          let _ = check ctx cm_default ftype in
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
    | DE.Match (DE.BLabel {dt_cases; dt_default}) ->
        with_locals ctx (fun ctx ->
          let map = Map.map dt_cases ~f:(fun _ -> fresh_local ctx `Flex ktype) in
          let param_row =
            Map.fold map
              ~init:begin match dt_default with
                | None -> all krow (fun r -> r)
                | Some _ -> fresh_local ctx `Flex krow
              end
              ~f:(fun ~key ~data r -> extend key data r)
          in
          let param = union param_row in
          let result = match dt_default with
            | None -> fresh_local ctx `Flex ktype
            | Some (None, body) ->
                synth ctx body
            | Some (Some v, body) ->
                synth
                  { ctx with vals_env = Map.set ctx.vals_env ~key:v ~data:param }
                  body
          in
          Map.iteri map ~f:(fun ~key ~data ->
            let (v, body) = Util.find_exn dt_cases key in
            let _ = check
                { ctx with vals_env = Map.set ctx.vals_env ~key:v ~data }
                body
                result
            in
            ()
          );
          (param **> result)
        )
    | DE.LetRec{letrec_types; letrec_vals; letrec_body} ->
        (* TODO: mutual recursion among types.
         *
         * This also doesn't currently handle dependencies among types at all, but
         * the plan for non-cyclic dependencies is to sort them topologically and
         * separate them out into separate let expressions in an earlier stage, so
         * we won't have to worry about that here.
        *)
        with_locals ctx (fun ctx ->
          let ctx = List.fold letrec_types ~init:ctx ~f:(fun ctx (v, ty) ->
              { ctx with type_env =
                           Map.set
                             ctx.type_env
                             ~key:v
                             ~data:(with_locals ctx (fun ctx -> make_type ctx ty))
              }
            )
          in
          let new_vars =
            List.map letrec_vals ~f:(fun (v, _) ->
              (v, fresh_local ctx `Flex ktype)
            )
          in
          let ctx' =
            List.fold new_vars ~init:ctx ~f:(fun ctx (vname, v) ->
              { ctx with vals_env = Map.set ctx.vals_env ~key:vname ~data: v }
            )
          in
          let checked_vals =
            List.map letrec_vals ~f:(fun (v, e) ->
              with_locals ctx' (fun ctx ->
                check ctx e (Util.find_exn ctx.vals_env v)
              )
            )
          in
          let checked_vals =
            List.map2_exn letrec_vals checked_vals ~f:(fun (v, _) ty ->
              (v, ty)
            )
          in
          let ctx =
            List.fold checked_vals ~init:ctx ~f:(fun ctx (v, ty) ->
              { ctx with vals_env = Map.set ctx.vals_env ~key:v ~data:ty }
            )
          in
          synth ctx letrec_body
        )
and check: context -> 'i DE.t -> u_var -> u_var =
  fun ctx e ty_want ->
  let ty_got = synth ctx e in
  require_subtype ctx ~sub:ty_got ~super:ty_want;
  ty_got
and require_subtype: context -> sub:u_var -> super:u_var -> unit =
  fun ctx ~sub ~super ->
  trace_req_subtype ~sub ~super;
  require_subtype_already_whnf ctx ~sub:(whnf sub) ~super:(whnf super);
  if Config.trace_require_subtype () then
    Caml.print_endline "Return."
and require_subtype_already_whnf: context -> sub:u_var -> super:u_var -> unit =
  fun ctx ~sub ~super ->
  let sub_id, super_id = get_id (UnionFind.get sub), get_id (UnionFind.get super) in
  if not (Set.mem !(ctx.assumptions) (sub_id, super_id)) then
    begin
      require_kind (get_kind sub) (get_kind super);
      ctx.assumptions := Set.add !(ctx.assumptions) (sub_id, super_id);
      begin match UnionFind.get sub, UnionFind.get super with
        | _ when UnionFind.equal sub super -> ()
        (* The UnionFind variables are different, but the IDs are the same. I(isd) am not
         * sure this can actually come up, but if it does, this is the behavior that
         * makes sense. *)
        | _ when sub_id = super_id -> UnionFind.merge (fun _ r -> r) sub super

        | `Free({ty_flag = `Flex; ty_id = l_id}, kl), `Free({ty_flag = `Flex; ty_id = r_id }, kr) ->
            (* Both sides are flexible variables; merge them, using the larger of their
             * scopes. *)
            require_kind kl kr;
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
            MuleErr.throw (`TypeError(`PermissionErr `Graft))

        (* Mismatched named constructors are never reconcilable: *)
        | `Const(_, `Named n, _, _), `Const(_, `Named m, _, _) when not (Poly.equal n m) ->
            MuleErr.throw (`TypeError (`MismatchedCtors (`Named n, `Named m)))

        (* All of the zero-argument consts unify with themselves; if the above case
         * didn't cover this one, then we're good: *)
        | `Const(_, `Named _, [], _), `Const(_, `Named _, [], _) -> ()

        (* Functions. *)
        | `Const(_, `Named `Fn, [psub, _; rsub, _], _),
          `Const(_, `Named `Fn, [psuper, _; rsuper, _], _) ->
            (* Note the flipped sub vs. super in the parameter case; this is standard
             * contravariance. *)
            require_subtype ctx ~sub:psuper ~super:psub;
            require_subtype ctx ~sub:rsub ~super:rsuper

        | `Const (_, `Named `Fn, x, _), `Const (_, `Named `Fn, y, _) ->
            wrong_num_args `Fn 2 x y

        | `Const(_, `Named `Union, [row_sub, _], _),
          `Const(_, `Named `Union, [row_super, _], _) ->
            require_subtype ctx ~sub:row_sub ~super:row_super

        | `Const(_, `Named `Union, x, _), `Const(_, `Named `Union, y, _) ->
            wrong_num_args `Union 1 x y

        | `Const(_, `Named `Record, [rtype_sub, _; rvals_sub, _], _),
          `Const(_, `Named `Record, [rtype_super, _; rvals_super, _], _) ->
            require_subtype ctx ~sub:rtype_sub ~super:rtype_super;
            require_subtype ctx ~sub:rvals_sub ~super:rvals_super

        | `Const(_, `Named `Record, x, _), `Const(_, `Named `Record, y, _) ->
            wrong_num_args `Record 2 x y

        | `Const(_, `Extend _, _, _), `Const(_, `Extend _, _, _) ->
            require_subtype_extend ctx ~sub ~super

        | `Const(_, `Named `Lambda, [pl, kpl; bl, kbl], _),
          `Const(_, `Named `Lambda, [pr, kpr; br, kbr], _) ->
            require_kind kpl kpr;
            require_kind kbl kbr;
            (* Substitue the same rigid variable for both lambdas'
             * parameters, and then check the bodies: *)
            let p = fresh_local ctx `Rigid kpl in
            require_subtype ctx
              ~sub:(subst
                  ~target:(get_id (UnionFind.get pl))
                  ~replacement:p
                  bl
              )
              ~super:(subst
                  ~target:(get_id (UnionFind.get pr))
                  ~replacement:p
                  br
              )
        | `Const(_, `Named c, _, _), _ | _, `Const(_, `Named c, _, _) ->
            MuleErr.bug ("Unknown type constructor: " ^ string_of_typeconst_name c)

        | _ ->
            MuleErr.bug "TODO: require_subytpe"
      end
    end
and require_subtype_extend ctx ~sub ~super =
  let fold_row side =
    let rec go m row =
      require_kind (get_kind row) krow;
      let row = whnf row in
      match UnionFind.get row with
      | `Quant(_, q, v, k, body) ->
          go m (unroll_quant ctx side q v k body)
      | `Const(_, `Extend lbl, [h, hk; t, tk], k) ->
          require_kind krow k;
          require_kind krow tk;
          go
            (Map.update m lbl ~f:(function
                  | None -> (h, hk)
                  | Some v -> v
                ))
            t
      | _ ->
          (m, row)
    in
    go LabelMap.empty
  in
  let unfold_row fields tail =
    List.fold fields ~init:tail ~f:(fun t (lbl, (h, hk)) ->
      UnionFind.make
        (`Const
            ( Gensym.gensym()
            , `Extend lbl
            , [h, hk; t, krow]
            , krow
            )
        )
    )
  in
  let (sub_fields, sub_tail) = fold_row `Sub sub in
  let (super_fields, super_tail) = fold_row `Super super in
  let sub_only = ref [] in
  let super_only = ref [] in
  Map.iter2 sub_fields super_fields ~f:(fun ~key ~data -> match data with
    | `Left v -> sub_only := (key, v) :: !sub_only
    | `Right v -> super_only := (key, v) :: !super_only
    | `Both ((sub_t, sub_k), (super_t, super_k)) ->
        require_kind sub_k super_k;
        require_subtype ctx ~sub:sub_t ~super:super_t
  );
  require_subtype ctx ~sub:sub_tail ~super:(unfold_row !super_only super_tail);
  require_subtype ctx ~sub:(unfold_row !sub_only sub_tail) ~super:super_tail
and trace_req_subtype ~sub ~super =
  if Config.trace_require_subtype () then
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
and with_kind k u = require_kind k (get_kind u); u
and require_kind l r = UnionFind.merge unify_kind l r
and unify_kind l r =
  begin match l, r with
    | `Free n, k | k, `Free n -> kind_occurs_check n k; k
    | `Type, `Type | `Row, `Row -> r
    | `Arrow(pl, pr), `Arrow(rl, rr) ->
        UnionFind.merge unify_kind pl pr;
        UnionFind.merge unify_kind rl rr;
        r
    | _ ->
        MuleErr.throw (`TypeError(`MismatchedKinds (Extract.kind l, Extract.kind r)))
  end
and kind_occurs_check: int -> u_kind -> unit =
  fun n -> function
    | `Free m when n = m ->
        MuleErr.throw (`TypeError `OccursCheckKind)
    | `Free _ | `Type | `Row -> ()
    | `Arrow(x, y) ->
        kind_occurs_check n (UnionFind.get x);
        kind_occurs_check n (UnionFind.get y)
and whnf: u_var -> u_var =
  fun t ->
  match UnionFind.get t with
  | `Quant(qid, q, v, k, body) ->
      UnionFind.set
        (`Quant(qid, q, v, k, whnf body))
        t;
      t
  | `Const(_, `Named `Apply, [f, fk; x, xk], k) ->
      require_kind (UnionFind.make(`Arrow(xk, k))) fk;
      apply_type t f x;
      whnf t
  | _ -> t
and apply_type app f arg =
  match UnionFind.get (whnf f) with
  | `Const(_, `Named `Lambda, [p, _; body, _], _) ->
      let result =
        subst body ~target:(get_id (UnionFind.get p)) ~replacement:arg
      in
      UnionFind.merge (fun _ r -> r) app result
  | _ -> ()

let rec gen_kind = function
  | `Arrow(p, r) -> UnionFind.make (`Arrow(gen_kind p, gen_kind r))
  | `Type -> ktype
  | `Row -> krow
  | `Unknown -> gen_k ()

let typecheck exp =
  DE.map exp ~f:gen_kind
  |> synth (make_initial_context ())
  |> Extract.get_var_type
