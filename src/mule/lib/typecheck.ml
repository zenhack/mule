include Typecheck_t

open Typecheck_types

module DE = Desugared_ast_expr
module DT = Desugared_ast_type
module C = Common_ast.Const
module Label = Common_ast.Label
module Var = Common_ast.Var

module IntPair = Pair.Make(Int)(Int)

type 'v var_map = (Var.t, 'v, Var.comparator_witness) Map.t

type context = {
  type_env : u_var var_map;
  vals_env : u_var var_map;
  locals : u_var list ref;

  (* [assumptions] is a list of subtyping constraints we've already seen.
   * This is used when checking subtyping constraints that may involve
   * recursive types -- if we are asked to check a subtyping constraint
   * that's already in our assumptions, we just return.
   *
   * Note that from a logician's standpoint this sounds incredibly fishy
   * -- but that's as expected; recursive types amount to circular
   * reasoning.
  *)
  assumptions : (IntPair.t, IntPair.comparator_witness) Set.t ref;
  scope : Scope.t;

  get_import_type : Paths_t.t -> u_var;
}

module Graphviz = struct
  let once_for_id seen id ~f =
    if not (Set.mem !seen id) then
      begin
        seen := Set.add !seen id;
        f ()
      end

  let emit_constraint_edge ldir lv rdir rv =
    let lid, rid = get_id (UnionFind.get lv), get_id (UnionFind.get rv) in
    match (ldir, lid, rdir, rid) with
    | `Sub, sub, `Super, super
    | `Super, super, `Sub, sub ->
        Debug.show_edge `Instance super sub
    | _ ->
        (* TODO: distinguish meet vs. join *)
        Debug.show_edge `Unify lid rid

  let emit_bound_var seen {bv_id; _} =
    once_for_id seen bv_id ~f:(fun () ->
      Debug.show_node `Bound bv_id
    )

  let emit_siblings_edges args =
    let args =
      List.map args ~f:(fun (uv, _) -> get_id (UnionFind.get uv))
    in
    match args with
    | [] -> ()
    | (x :: xs) ->
        List.fold_left xs ~init:x ~f:(fun l r ->
          Debug.show_edge `Sibling l r; r
        )
        |> ignore

  let rec emit_u_var seen uv =
    let u = UnionFind.get uv in
    let u_id = get_id u in
    once_for_id seen u_id ~f:begin fun () ->
      match u with
      | `Const(_, c, args, _) ->
          Debug.show_node (`Const c) u_id;
          List.iter args ~f:(fun (ty, _) ->
            emit_u_var seen ty;
            Debug.show_edge `Structural u_id (get_id (UnionFind.get ty));
          );
          emit_siblings_edges args
      | `Bound bv -> emit_bound_var seen bv
      | `Quant {q_quant; q_var = {bv_id; _} as bv; q_body; _} ->
          Debug.show_node (`Quant q_quant) u_id;
          emit_bound_var seen bv;
          emit_u_var seen q_body;
          Debug.show_edge `Structural u_id bv_id;
          Debug.show_edge (`Binding `Explicit) u_id bv_id;
          let body_id = get_id (UnionFind.get q_body) in
          Debug.show_edge `Structural u_id body_id;
          Debug.show_edge `Sibling bv_id body_id
      | `Free {ty_id; ty_flag; _} ->
          (* TODO: display scope. *)
          Debug.show_node (`Free ty_flag) ty_id
    end

  (* This traverses the contexts and emtis everything reachable from it.
   * we are not currently using it, because this ends up printing out the
   * types of all the builtins too, which is too much clutter.
     let emit_ctx seen ctx =
     Map.iter ctx.type_env ~f:(emit_u_var seen);
     Map.iter ctx.vals_env ~f:(emit_u_var seen);
     List.iter !(ctx.locals) ~f:(fun v -> emit_u_var seen v)
  *)
end

let cant_instantiate info other_ty ~path ~reason =
  MuleErr.throw
    (`TypeError
        (`CantInstantiate {
              ci_info = info;
              ci_other =
                begin match UnionFind.get (get_kind other_ty) with
                  | `Row -> `Row (Extract.get_var_row other_ty)
                  | _ -> `Type (Extract.get_var_type other_ty)
                end;
              ci_path = path;
              ci_reason = reason;
            }))

let throw_mismatch ~path ~reason ~sub ~super =
  MuleErr.throw
    (`TypeError
        (`MismatchedCtors {
              se_sub = Extract.get_var_type sub;
              se_super = Extract.get_var_type super;
              se_path = path;
              se_reason = reason;
            }))

let flip_dir = function
  | `Sub -> `Super
  | `Super -> `Sub

let unbound_var v =
  MuleErr.throw (`UnboundVar v)

let apply_kids: u_type -> f:(u_var -> u_var) -> u_type =
  fun  t ~f -> match t with
    | `Free _ -> t
    | `Bound _ -> t
    | `Quant q ->
        `Quant { q with q_body = f q.q_body }
    | `Const(c_id, c, args, k) ->
        `Const(c_id, c, List.map args ~f:(fun (t, k) -> (f t, k)), k)

(* [hoist_scope scope uv] adjusts [uv] so that all of the free
 * variables underneath it have a scope at least as great as [scope]. *)
let hoist_scope: Scope.t -> u_var -> unit =
  fun scope uv ->
  let seen = ref (Set.empty (module Int)) in
  let rec go : u_var -> unit = fun uv ->
    let u = UnionFind.get uv in
    let id = get_id u in
    if not (Set.mem !seen id) then
      begin
        seen := Set.add !seen id;
        match u with
        | `Free tv ->
            UnionFind.set
              (`Free{tv with ty_scope = Scope.lca scope tv.ty_scope})
              uv
        | `Bound _ -> ()
        | `Quant {q_body; _} ->
            go q_body
        | `Const(_, _, args, _) ->
            List.iter args ~f:(fun (t, _) -> go t)
      end
  in
  go uv

let rec subst ~target ~replacement uv =
  (* Nodes we've already seen, to detect cycles and avoid traversing
   * shared sub-graphs. *)
  let seen = ref (Map.empty (module Int)) in
  let rec go uv =
    begin match UnionFind.get uv with
      | u when get_id u = target -> replacement
      | u when Map.mem !seen (get_id u) -> Util.find_exn !seen (get_id u)
      | `Free _ | `Bound _ -> uv
      | `Quant q when q.q_var.bv_id = target ->
          (* Shadowing the target; stop here. *)
          uv
      | u ->
          (* Add an entry to `seen` before traversing, in case we hit
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
  | `Free _ | `Bound _ -> MuleErr.bug "impossible"
  | `Const(_, c, args, k) -> `Const(Gensym.gensym (), c, args, k)
  | `Quant q ->
      let bv = { q.q_var with bv_id = Gensym.gensym () } in
      `Quant {
        q with
        q_id = Gensym.gensym ();
        q_var = bv;
        q_body =
          subst q.q_body
            ~target:q.q_var.bv_id
            ~replacement:(UnionFind.make (`Bound bv))
      }

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
  let scope = Scope.make_child ctx.scope in
  let result = f { ctx with locals = new_locals; scope } in
  let (_grafted, raised, to_generalize) =
    List.partition3_map !new_locals ~f:(fun v ->
      match UnionFind.get v with
      | `Free{ty_id; ty_scope; ty_flag; ty_info; ty_kind = k} when Scope.equal ty_scope scope ->
          let q = match ty_flag with
            | `Flex -> `All
            | `Rigid -> `Exist
          in
          let bv = {
            bv_id = ty_id;
            bv_info = { ty_info with vi_binder = Some (`Quant q) };
            bv_kind = k;
          }
          in
          `Trd (fun acc ->
            UnionFind.make
              (`Quant {
                    q_id = Gensym.gensym ();
                    q_quant = q;
                    q_var = bv;
                    q_kind = k;
                    q_body =
                      subst acc
                        ~target:ty_id
                        ~replacement:(UnionFind.make (`Bound bv));
                  })
          )
      | `Free _ -> `Snd v
      | _ -> `Fst ()
    )
  in
  ctx.locals := raised @ !(ctx.locals);
  List.fold to_generalize ~init:result ~f:(fun acc f -> f acc)

(* Create a new local with the given flag and kind. *)
let fresh_local ?(vinfo={vi_name = None; vi_binder = None}) ctx ty_flag k =
  let ty_id = Gensym.gensym () in
  let ty_scope = ctx.scope in
  let v = UnionFind.make (`Free {
      ty_id;
      ty_flag;
      ty_scope;
      ty_info = vinfo;
      ty_kind = k;
    })
  in
  ctx.locals := v :: !(ctx.locals);
  v

let synth_const: C.t -> u_var = function
  | C.Integer _ -> int
  | C.Text _ -> text
  | C.Char _ -> char

let find_bound ~env ~var ~src = match Map.find env var with
  | Some value -> value
  | None ->
      begin match src with
        | `Sourced v -> unbound_var v
        | `Generated ->
            MuleErr.bug ("Unbound internally-generated variable: " ^ Var.to_string var)
      end

(* Build an initial context, which contains types for the stuff in intrinsics. *)
let rec make_initial_context ~get_import_type =
  let assumptions = ref (Set.empty (module IntPair)) in
  let scope = Scope.empty in
  let dummy = {
    type_env = Map.empty (module Var);
    vals_env = Map.empty (module Var);
    locals = ref [];
    assumptions;
    scope;
    get_import_type;
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
  {
    type_env;
    vals_env;
    locals = ref [];
    assumptions;
    scope;
    get_import_type;
  }

and with_rec_binds ctx DE.{rec_types; rec_vals} f =
  (* TODO: mutual recursion among types. *)
  let ctx = List.fold (List.concat rec_types) ~init:ctx ~f:(fun ctx (v, ty) ->
      { ctx with type_env =
                   Map.set
                     ctx.type_env
                     ~key:v
                     ~data:(with_locals ctx (fun ctx -> make_type ctx ty))
      }
    )
  in
  let new_vars =
    List.map rec_vals ~f:(fun (v, _) ->
      (v, fresh_local ctx `Flex ktype)
    )
  in
  let ctx' =
    List.fold new_vars ~init:ctx ~f:(fun ctx (vname, v) ->
      { ctx with vals_env = Map.set ctx.vals_env ~key:vname ~data:v }
    )
  in
  let checked_vals =
    List.map rec_vals ~f:(fun (v, e) ->
      with_locals ctx' (fun ctx ->
        check ctx
          e
          (Util.find_exn ctx.vals_env v)
          ~reason:(NonEmpty.singleton `Unspecified)
      )
      |> unpack_exist ctx
    )
  in
  let checked_vals =
    List.map2_exn rec_vals checked_vals ~f:(fun (v, _) ty ->
      (v, ty)
    )
  in
  let ctx =
    List.fold checked_vals ~init:ctx ~f:(fun ctx (v, ty) ->
      { ctx with vals_env = Map.set ctx.vals_env ~key:v ~data:ty }
    )
  in
  f ctx
(* Turn a type in the AST into a type in the type checker: *)
and make_type ctx ty = match ty with
  | DT.Var {v_var; v_src; _} ->
      find_bound
        ~env:ctx.type_env
        ~var:v_var
        ~src:v_src
  | DT.Quant {q_quant; q_var; q_body; _} ->
      quant ~vname:(Var.to_string q_var) q_quant (gen_k ()) (fun v ->
        make_type
          { ctx with type_env = Map.set ctx.type_env ~key:q_var ~data:v }
          q_body
      )
  | DT.Opaque _ ->
      MuleErr.bug "Opaques should have been qualified before typechecking."
  | DT.Named{n_name; _} ->
      const_ty n_name
  | DT.Record{r_types; r_values; _} ->
      record
        (make_row ctx (`Record `Type) r_types)
        (make_row ctx (`Record `Value) r_values)
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
      union (make_row ctx `Union u_row)
  | DT.Recur{mu_var; mu_body; _} ->
      let t = recur ~vname:(Var.to_string mu_var) (fun v ->
          make_type
            { ctx with type_env = Map.set ctx.type_env ~key:mu_var ~data:v }
            mu_body
        )
      in
      require_kind (get_kind t) ktype;
      t
  | DT.TypeLam{tl_param; tl_body; _} ->
      lambda ~vname:(Var.to_string tl_param) (gen_k ()) (fun p ->
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
  | DT.Path{p_var; p_lbls; p_src; _} ->
      let var_type =
        begin match p_var with
          | `Var var ->
              find_bound
                ~env:ctx.vals_env
                ~var
                ~src:begin match p_src with
                  | `Generated -> `Generated
                  | `Sourced Common_ast.Loc.{l_loc; _} ->
                      `Sourced (Common_ast.Loc.{
                          l_value = var;
                          l_loc;
                        })
                end
              |> with_kind ktype
          | `Import {i_resolved_path; _} ->
              ctx.get_import_type i_resolved_path
        end
      in
      let result_type = fresh_local ctx `Flex (gen_k ()) in
      let path_type = make_path_type result_type p_lbls in
      require_subtype
        ctx
        ~reason:(NonEmpty.singleton (`Path p_src))
        ~sub:var_type
        ~super:path_type;
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
  | `Quant {q_quant = `Exist; q_var = {bv_id; bv_info; _}; q_kind; q_body; _} ->
      strip_param_exists ctx (
        subst
          q_body
          ~target:bv_id
          ~replacement:(fresh_local ctx `Flex q_kind ~vinfo:bv_info)
      )
  | _ ->
      pty
and make_row ctx parent {row_fields; row_rest; _} =
  let tail = match row_rest, parent with
    | None, `Record `Type | None, `Union -> all krow (fun x -> x)
    | None, `Record `Value -> empty
    | Some t, _ -> with_kind krow (make_type ctx t)
  in
  List.fold_right row_fields ~init:tail ~f:(fun (lbl, ty) rest ->
    extend lbl (make_type ctx ty) rest
  )
and synth: context -> 'i DE.t -> u_var =
  fun ctx e ->
  let result = begin match e with
    | DE.Const {const_val} -> synth_const const_val
    | DE.Embed _ -> text
    | DE.Import {i_resolved_path; _} ->
        ctx.get_import_type i_resolved_path
    | DE.Var {v_var; v_src} ->
        find_bound ~env:ctx.vals_env ~var:v_var ~src:v_src
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
    | DE.GetField{gf_lbl; gf_record} ->
        with_locals ctx (fun ctx ->
          let head = fresh_local ctx `Flex ktype in
          let tail = fresh_local ctx `Flex krow in
          let rt = fresh_local ctx `Flex krow in
          ignore
            (check ctx
                gf_record
                (record rt (extend gf_lbl head tail))
                ~reason:(NonEmpty.singleton (`GetField(gf_lbl, gf_record))));
          head
        )
    | DE.UpdateVal {uv_lbl; uv_val; uv_record} ->
        with_locals ctx (fun ctx ->
          let rt = fresh_local ctx `Flex krow in
          let rv = fresh_local ctx `Flex krow in
          ignore
            (check ctx
                uv_record
                (record rt rv)
                ~reason:(NonEmpty.singleton (`RecordUpdate e)));
          let val_t = synth ctx uv_val in
          record rt (extend uv_lbl val_t rv)
        )
    | DE.UpdateType {ut_lbl; ut_type; ut_record} ->
        with_locals ctx (fun ctx ->
          let rv = fresh_local ctx `Flex krow in
          let rt = fresh_local ctx `Flex krow in
          let _ =
            check ctx
              ut_record
              (record rt rv)
              ~reason:(NonEmpty.singleton (`RecordUpdate e))
          in
          record (extend ut_lbl (make_type ctx ut_type) rt) rv
        )
    | DE.Record r ->
        with_locals ctx (fun ctx ->
          with_rec_binds ctx r (fun ctx ->
            let build_row env fields init =
              let fields = List.map fields ~f:(fun (v, _) ->
                  (v, Util.find_exn env v)
                )
              in
              List.fold fields ~init ~f:(fun tail (v, t) ->
                extend (Common_ast.var_to_label v) t tail
              )
            in
            record
              (build_row ctx.type_env (List.concat r.rec_types) (all krow (fun r -> r)))
              (build_row ctx.vals_env r.rec_vals empty)
          )
        )
    | DE.Ctor{c_lbl; c_arg} ->
        let arg_t = synth ctx c_arg in
        union (extend c_lbl arg_t (all krow (fun r -> r)))
    | DE.WithType {wt_src; wt_expr; wt_type} ->
        let want_ty = make_type ctx wt_type |> with_kind ktype in
        let _ = check ctx
            wt_expr
            want_ty
            ~reason:(NonEmpty.singleton (`TypeAnnotation(wt_src, wt_type)))
        in
        want_ty
    | DE.Let{let_v; let_e; let_body} ->
        let ty = unpack_exist ctx (synth ctx let_e) in
        synth
          { ctx
            with vals_env = Map.set ctx.vals_env ~key:let_v ~data:ty
          }
          let_body
    | DE.App{app_fn; app_arg} ->
        with_locals ctx (fun ctx ->
          let p = synth ctx app_arg in
          let r = fresh_local ctx `Flex ktype in
          let _ = check ctx
              app_fn
              (p **> r)
              ~reason:(NonEmpty.singleton (`ApplyFn(app_fn, app_arg, p)))
          in
          r
        )
    | DE.Match b ->
        with_locals ctx (fun ctx ->
          let (p, r) = synth_branch ctx b in
          p **> r
        )
    | DE.LetRec{letrec_binds; letrec_body} ->
        with_locals ctx (fun ctx ->
          with_rec_binds ctx letrec_binds (fun ctx ->
            synth ctx letrec_body
          )
        )
  end
  in
  if Config.render_constraint_graph () then
    begin
      Debug.start_graph ();
      Graphviz.emit_u_var (ref (Set.empty (module Int))) result;
      Debug.set_root (get_id (UnionFind.get result));
      Debug.end_graph()
    end;
  result
and synth_branch ctx ?have_default:(have_default=false) b =
  match b with
  | DE.BLeaf lf ->
      let param = fresh_local ctx `Flex ktype in
      let result = fresh_local ctx `Flex ktype in
      ignore (check_leaf ctx lf (param **> result));
      (param, result)
  | DE.BConst {cm_cases; cm_default} ->
      let param = fresh_local ctx `Flex ktype in
      let result =
        Option.map cm_default ~f:(fun lf ->
          let result = fresh_local ctx `Flex ktype in
          ignore (check_leaf ctx lf (param **> result));
          result
        )
      in
      let result = match result with
        | Some r -> r
        | None -> fresh_local ctx `Flex ktype
      in
      Map.fold cm_cases
        ~init:(param, result)
        ~f:(fun ~key ~data (param, result) ->
          ignore (check_const ctx key param);
          let result = join ctx
              ~reason:(NonEmpty.singleton `Unspecified)
              result
              (synth ctx data)
          in
          (param, result)
        )
  | DE.BLabel {lm_cases; lm_default} ->
      let map = Map.map lm_cases ~f:(
          synth_branch
            ctx
            ~have_default:(have_default || Option.is_some lm_default)
        )
      in
      let (param_row, result) =
        let result = fresh_local ctx `Flex ktype in
        Map.fold map
          ~init:begin match lm_default with
            | None when have_default -> (empty, result)
            | None -> (all krow (fun r -> r), result)
            | Some lf ->
                let row = fresh_local ctx `Flex krow in
                ignore (check_leaf ctx lf (union row **> result));
                (row, result)
          end
          ~f:(fun ~key ~data:(param, data) (row, result) ->
            ( extend key param row
            , join ctx ~reason:(NonEmpty.singleton `Unspecified) data result
            )
          )
      in
      (union param_row, result)
and synth_leaf ctx DE.{lf_var; lf_body} =
  with_locals ctx (fun ctx ->
    let pat = fresh_local ctx `Flex ktype in
    match lf_var with
    | None -> pat **> synth ctx lf_body
    | Some v ->
        pat
        **> synth
          { ctx with vals_env = Map.set ctx.vals_env ~key:v ~data:pat }
          lf_body
  )
and check: context -> reason:(MuleErr.subtype_reason NonEmpty.t) -> 'i DE.t -> u_var -> u_var =
  fun ctx ~reason e ty_want ->
  if Config.render_constraint_graph () then
    begin
      Debug.start_graph ();
      Graphviz.emit_u_var (ref (Set.empty (module Int))) ty_want;
      Debug.set_root (get_id (UnionFind.get ty_want));
      Debug.end_graph ()
    end;
  require_kind (get_kind ty_want) ktype;
  match e with
  | DE.Let{let_v; let_e; let_body} ->
      let ty_e = synth ctx let_e in
      check
        { ctx with vals_env = Map.set ctx.vals_env ~key:let_v ~data:ty_e }
        let_body
        ty_want
        ~reason
  | DE.App{app_fn; app_arg} ->
      let p = synth ctx app_arg in
      ignore
        (check ctx
            app_fn
            (p **> ty_want)
            ~reason:(NonEmpty.cons (`ApplyFn(app_fn, app_arg, p)) reason));
      ty_want
  | DE.WithType{wt_src; wt_expr; wt_type} ->
      let ty_want_inner = make_type ctx wt_type |> with_kind ktype in
      let ty_want_outer = ty_want in
      (* Verify that the annotation is a subtype of our desired type, then
       * check that the annotation is correct.
       *
       * Note that the order here is /critical/; if ty_want_outer is a
       * flexible variable, checking the annotation first may cause it
       * to be unified with something during the check, which may either
       * cause typechecking to erroneously fail, or yield a more specific
       * type than necessary. *)
      require_subtype
        ctx
        ~reason
        ~sub:ty_want_inner
        ~super:ty_want_outer;
      ignore
        (check ctx
            wt_expr
            ty_want_inner
            ~reason:(NonEmpty.singleton (`TypeAnnotation(wt_src, wt_type))));
      ty_want_outer
  | DE.Lam{l_param; l_body} ->
      with_locals ctx (fun ctx ->
        check_maybe_flex ctx e ty_want ~f:(fun want -> match UnionFind.get want with
          | `Const(_, `Named `Fn, [p, _; r, _], _) ->
              let body =
                check
                  { ctx with vals_env = Map.set ctx.vals_env ~key:l_param ~data:p }
                  l_body
                  r
                  ~reason:(NonEmpty.singleton `Unspecified)
              in
              (p **> body)
          | _ ->
              let sub, super = synth ctx e, ty_want in
              let path = TypePath.base sub super in
              throw_mismatch
                ~sub
                ~super
                ~path
                ~reason
        )
      )
  | DE.Match b ->
      with_locals ctx (fun ctx ->
        check_maybe_flex ctx e ty_want ~f:(fun want -> match UnionFind.get want with
          | `Const(_, `Named `Fn, [p, _; r, _], _) ->
              check_branch ctx b (p, r)
          | _ ->
              let sub, super = synth ctx e, ty_want in
              let path = TypePath.base sub super in
              throw_mismatch
                ~sub
                ~super
                ~path
                ~reason
        )
      )
  | DE.Record r ->
      with_locals ctx (fun ctx ->
        check_maybe_flex ctx e ty_want  ~f:(fun want -> match UnionFind.get want with
          | `Const(_, `Named `Record, [tys, _; vals, _], _) ->
              check_record ctx r tys vals ~reason
          | _ ->
              let sub, super = synth ctx e, ty_want in
              let path = TypePath.base sub super in
              throw_mismatch
                ~sub
                ~super
                ~path
                ~reason
        )
      )
  | _ ->
      let ty_got = synth ctx e in
      require_subtype
        ctx
        ~reason
        ~sub:ty_got
        ~super:ty_want;
      ty_got
and check_maybe_flex ctx e ty_want ~f =
  let want = unroll_all_quants ctx `Super (whnf ty_want) in
  match UnionFind.get want with
  | `Free{ty_flag = `Flex; ty_kind; _} ->
      require_kind ty_kind ktype;
      let got = synth ctx e in
      UnionFind.merge (fun _ r -> r) want got;
      got
  | _ ->
      f want
and check_record ctx DE.{rec_types; rec_vals} want_types want_vals ~reason =
  (* TODO: handle mutually recursive types. *)
  let (have_types_row, ctx) =
    List.fold_left
      (List.concat rec_types)
      ~init:( all krow (fun x -> x)
            , ctx
            )
      ~f:(fun (r, ctx) (v, t) ->
        let t' = make_type ctx t in
        let r' = extend (Common_ast.var_to_label v) t' r in
        (r', { ctx with type_env = Map.set ctx.type_env ~key:v ~data:t' })
      )
  in
  require_subtype
    ctx
    ~sub:have_types_row
    ~super:want_types
    ~reason:(NonEmpty.singleton `Unspecified);
  let (have_vals_row, have_vals_exp_map, ctx) =
    List.fold_left
      rec_vals
      ~init:( empty
            , Map.empty (module Var)
            , ctx
            )
      ~f:(fun (row, exp_map, ctx) (v, e) ->
        let tyvar = fresh_local ctx `Flex ktype in
        ( extend (Common_ast.var_to_label v) tyvar row
        , Map.set exp_map ~key:v ~data:e
        , { ctx with vals_env = Map.set ctx.vals_env ~key:v ~data:tyvar }
        )
      )
  in
  require_subtype
    ctx
    ~sub:have_vals_row
    ~super:want_vals
    ~reason:(NonEmpty.singleton `Unspecified);
  Map.iteri have_vals_exp_map ~f:(fun ~key ~data ->
    let t = Util.find_exn ctx.vals_env key in
    ignore (check ctx data t ~reason)
  );
  record have_types_row have_vals_row
and check_branch: context -> 'i DE.branch -> ?default:u_var -> (u_var * u_var) -> u_var =
  fun ctx b ?default (p_want, r_want) ->
  let ty_want = p_want **> r_want in
  match b with
  | DE.BLeaf lf ->
      check_leaf ctx lf ty_want
  | DE.BConst {cm_cases; cm_default} ->
      begin match default, cm_default with
        | None, None -> MuleErr.throw `IncompletePattern
        | Some _, None -> ()
        | _, Some lf -> ignore (check_leaf ctx lf ty_want)
      end;
      Map.iteri cm_cases ~f:(fun ~key ~data ->
        check_const ctx key p_want;
        ignore (check ctx data r_want ~reason:(NonEmpty.singleton `Unspecified));
      );
      ty_want
  | DE.BLabel {lm_cases; lm_default} ->
      let default = match lm_default with
        | None -> default
        | Some _ -> Some ty_want
      in
      Option.iter lm_default ~f:(fun lf -> ignore (check_leaf ctx lf ty_want));
      let p_lbls = union (make_match_row ctx
            ~have_default:(Option.is_some default)
            lm_cases
            lm_default
        )
      in
      require_subtype ctx
        ~sub:p_want
        ~super:p_lbls
        ~reason:(NonEmpty.singleton `Unspecified);
      Map.iteri lm_cases ~f:(fun ~key ~data ->
        let u_hd = fresh_local ctx `Flex ktype in
        let u_tl = fresh_local ctx `Flex krow in
        require_subtype
          ctx
          ~sub:p_want
          ~super:(union (extend key u_hd u_tl))
          ~reason:(NonEmpty.singleton `Unspecified);
        ignore (check_branch ctx data ?default (u_hd, r_want))
      );
      ty_want
and make_match_row ctx ~have_default lm_cases lm_default =
  Map.fold lm_cases
    ~init:begin match lm_default with
      | None when have_default -> empty
      | None -> all krow (fun r -> r)
      | Some _ -> fresh_local ctx `Flex krow
    end
    ~f:(fun ~key ~data:_ tl ->
      extend key (fresh_local ctx `Flex ktype) tl
    )
and check_leaf: context -> 'i DE.leaf -> u_var -> u_var =
  fun ctx lf ty_want ->
  let ty_got = synth_leaf ctx lf in
  require_subtype
    ctx
    ~reason:(NonEmpty.singleton `Unspecified)
    ~sub:ty_got
    ~super:ty_want;
  ty_got
and require_subtype
  : context
    -> reason:(MuleErr.subtype_reason NonEmpty.t)
    -> sub:u_var
    -> super:u_var
    -> unit =
  fun ctx ~reason ~sub ~super ->
  ignore (unify ctx
      ~path:(TypePath.base sub super)
      ~reason
      (sub, `Sub)
      (super, `Super)
  )
and unify =
  fun ctx ~reason (sub, sub_dir) (super, super_dir) ->
  trace_req_subtype ~sub ~super;
  let result =
    unify_already_whnf ctx ~reason (whnf sub, sub_dir) (whnf super, super_dir)
  in
  if Config.trace_require_subtype () then
    Stdio.print_endline "Return.";
  result
and unify_already_whnf
  : context
    -> path:TypePath.t
    -> reason:(MuleErr.subtype_reason NonEmpty.t)
    -> (u_var * subtype_side)
    -> (u_var * subtype_side)
    -> u_var =
  fun ctx ~path ~reason (sub, sub_dir) (super, super_dir) ->
  if Config.render_constraint_graph () then
    begin
      Debug.start_graph ();
      let seen = ref (Set.empty (module Int)) in
      Graphviz.emit_u_var seen sub;
      Graphviz.emit_u_var seen super;
      Graphviz.emit_constraint_edge sub_dir sub super_dir super;
      Debug.set_root (get_id (UnionFind.get super));
      (* Graphviz.emit_ctx seen ctx; *)
      Debug.end_graph ()
    end;
  let sub_id, super_id = get_id (UnionFind.get sub), get_id (UnionFind.get super) in
  if Set.mem !(ctx.assumptions) (sub_id, super_id) then
    sub
  else
    begin
      require_kind (get_kind sub) (get_kind super);
      ctx.assumptions := Set.add !(ctx.assumptions) (sub_id, super_id);
      begin match UnionFind.get sub, UnionFind.get super with
        | _ when UnionFind.equal sub super -> sub
        (* The UnionFind variables are different, but the IDs are the same. I(isd) am not
         * sure this can actually come up, but if it does, this is the behavior that
         * makes sense. *)
        | _ when sub_id = super_id ->
            UnionFind.merge (fun _ r -> r) sub super;
            sub

        | `Bound {bv_info = { vi_binder = Some `Rec; vi_name = Some var }; _}, _
        | _, `Bound {bv_info = { vi_binder = Some `Rec; vi_name = Some var }; _} ->
            (* This can happen if the user supplies the type `rec a. a`. Normally,
             * the rec-bound variable gets replaced with the body but if the variable
             * is ungarded like that it sticks around. *)
            MuleErr.bug ("TODO(better errors): unguarded recursive type: rec " ^ var ^ ". " ^ var)

        | _, `Bound _ | `Bound _, _ ->
            (* This should never happen. *)
            MuleErr.bug "Tried to unify distinct bound variables!"

        | `Free{ty_flag = `Flex; ty_id = l_id; ty_info = l_info; ty_scope = l_scope; ty_kind = kl; _},
          `Free{ty_flag = `Flex; ty_id = _   ; ty_scope = r_scope; ty_kind = kr; _} ->
            (* Both sides are flexible variables; merge them, using the lca of their
             * scopes. *)
            require_kind kl kr;
            UnionFind.merge
              (fun _ _ -> `Free {
                    ty_flag = `Flex;
                    ty_info = l_info;
                    ty_id = l_id;
                    ty_scope = Scope.lca l_scope r_scope;
                    ty_kind = kl;
                  })
              sub super;
            sub
        (* One side is flexible; set it equal to the other one. *)
        | `Free{ty_flag = `Flex; ty_scope; _}, _ ->
            hoist_scope ty_scope super;
            UnionFind.merge (fun _ r -> r) sub super;
            sub
        | _, `Free{ty_flag = `Flex; ty_scope; _} ->
            hoist_scope ty_scope sub;
            UnionFind.merge (fun l _ -> l) sub super;
            sub
        | `Quant q, _ ->
            unify
              ctx
              ~reason
              ~path:(TypePath.append path (`Unroll(q, `Left)))
              ( unroll_quant ctx sub_dir q
              , sub_dir
              )
              ( super
              , super_dir
              )
        | _, `Quant q ->
            unify ctx
              ~reason
              ~path:(TypePath.append path (`Unroll(q, `Right)))
              ( sub
              , sub_dir
              )
              ( unroll_quant ctx super_dir q
              , super_dir
              )

        (* Rigid variable should fail (If they were the same already, they would have been
         * covered above): *)
        | `Free{ty_flag = `Rigid; ty_info; _}, _ ->
            cant_instantiate ty_info super ~path ~reason
        | _, `Free{ty_flag = `Rigid; ty_info; _} ->
            cant_instantiate ty_info sub ~path ~reason

        (* Mismatched named constructors are never reconcilable: *)
        | `Const(_, `Named n, _, _), `Const(_, `Named m, _, _) when not (Poly.equal n m) ->
            MuleErr.throw
              (`TypeError
                  (`MismatchedCtors {
                        se_sub = Extract.get_var_type sub;
                        se_super = Extract.get_var_type super;
                        se_path = path;
                        se_reason = reason;
                      }))

        (* All of the zero-argument consts unify with themselves; if the above case
         * didn't cover this one, then we're good: *)
        | `Const(_, `Named _, [], _), `Const(_, `Named _, [], _) -> sub

        (* Functions. *)
        | `Const(_, `Named `Fn, [psub, _; rsub, _], _),
          `Const(_, `Named `Fn, [psuper, _; rsuper, _], _) ->
            (* Note the flipped direction in the parameter case; this is standard
             * contravariance. *)
            let param =
              unify ctx
                ~reason
                ~path:(TypePath.append path (`Fn `Param))
                (psuper, flip_dir super_dir)
                (psub, flip_dir sub_dir)
            in
            let result =
              unify ctx
                ~reason
                ~path:(TypePath.append path (`Fn `Result))
                (rsub, sub_dir)
                (rsuper, super_dir)
            in
            (param **> result)

        | `Const (_, `Named `Fn, x, _), `Const (_, `Named `Fn, y, _) ->
            wrong_num_args `Fn 2 x y

        | `Const(_, `Named `Union, [row_sub, _], _),
          `Const(_, `Named `Union, [row_super, _], _) ->
            union (
              unify ctx
                ~reason
                ~path:(TypePath.append path `UnionRow)
                (row_sub, sub_dir)
                (row_super, super_dir)
            )

        | `Const(_, `Named `Union, x, _), `Const(_, `Named `Union, y, _) ->
            wrong_num_args `Union 1 x y

        | `Const(_, `Named `Record, [rtype_sub, _; rvals_sub, _], _),
          `Const(_, `Named `Record, [rtype_super, _; rvals_super, _], _) ->
            let rtype =
              unify ctx
                (rtype_sub, sub_dir)
                (rtype_super, super_dir)
                ~reason
                ~path:(TypePath.append path (`RecordPart `Type))
            in
            let rvals =
              unify ctx
                (rvals_sub, sub_dir)
                (rvals_super, super_dir)
                ~reason
                ~path:(TypePath.append path (`RecordPart `Value))
            in
            record rtype rvals

        | `Const(_, `Named `Record, x, _), `Const(_, `Named `Record, y, _) ->
            wrong_num_args `Record 2 x y

        | `Const(_, `Extend _, _, _), `Const(_, `Extend _, _, _) ->
            unify_extend ctx
              ~reason
              ~path
              (sub, sub_dir)
              (super, super_dir)
        | `Const(_, `Named `Lambda, [pl, kpl; bl, kbl], _),
          `Const(_, `Named `Lambda, [pr, kpr; br, kbr], _) ->
            require_kind kpl kpr;
            require_kind kbl kbr;
            (* Substitue the same rigid variable for both lambdas'
             * parameters, and then check the bodies: *)
            let p = fresh_local ctx `Rigid kpl in
            let check p_old b_old =
              subst
                ~target:(get_id (UnionFind.get p_old))
                ~replacement:p
                b_old
            in
            let body =
              unify ctx
                (check pl bl, sub_dir)
                (check pr br, super_dir)
                ~reason
                ~path:(TypePath.append path `TypeLamBody)
            in
            lambda (get_kind p) (fun p' ->
              subst
                ~target:(get_id (UnionFind.get p))
                ~replacement:p'
                body
            )
        | `Const(_, `Named `Apply, [fl, flk; argl, arglk], retlk),
          `Const(_, `Named `Apply, [fr, frk; argr, argrk], retrk) ->
            require_kind flk frk;
            require_kind arglk argrk;
            require_kind retlk retrk;
            require_type_eq ctx fl fr;
            require_type_eq ctx argl argr;
            apply fl argl

        | _ ->
            let data =
              Sexp.List [
                Sexp.List [Sexp.Atom "sub"; sexp_of_uvar (Set.empty (module Int)) sub];
                Sexp.List [Sexp.Atom "super"; sexp_of_uvar (Set.empty (module Int)) super];
              ]
            in
            MuleErr.bug ("unify: did not handle case:\n" ^ (Sexp.to_string_hum data))
      end
    end
and unify_extend ctx ~path ~reason (sub, sub_dir) (super, super_dir) =
  let fold_row =
    let rec go m row =
      require_kind (get_kind row) krow;
      let row = whnf row in
      match UnionFind.get row with
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
    go (Map.empty (module Label))
  in
  let (sub_fields, sub_tail) = fold_row sub in
  let (super_fields, super_tail) = fold_row super in
  let sub_tail = ref sub_tail in
  let super_tail = ref super_tail in
  let single
      ~path
      tailref
      taildir
      lbldir
      lbl
      (ty, _kind)
    =
    let tail' =
      unify
        ctx
        ~reason
        ~path
        (extend lbl ty (fresh_local ctx `Flex krow), lbldir)
        (!tailref, taildir);
    in
    match UnionFind.get tail' with
    | `Const(_, `Extend _, [h, _; t, _], _) ->
        tailref := t;
        Some h
    | _ -> MuleErr.bug "impossible"
  in
  let merged =
    Map.merge sub_fields super_fields ~f:(fun ~key data ->
      let path = TypePath.append path (`RowLabel key) in
      match data with
      | `Left v ->
          single ~path super_tail super_dir sub_dir key v
      | `Right v ->
          single ~path sub_tail sub_dir super_dir key v
      | `Both ((sub_t, sub_k), (super_t, super_k)) ->
          require_kind sub_k super_k;
          Some (
            unify
              ctx
              ~reason
              ~path
              (sub_t, sub_dir)
              (super_t, super_dir)
          )
    )
  in
  let tail =
    unify ctx
      ~reason
      ~path:(TypePath.append path `RowTail)
      (!sub_tail, sub_dir)
      (!super_tail, super_dir)
  in
  Map.fold merged
    ~init:tail
    ~f:(fun ~key ~data tail ->
      extend key data tail
    )
and trace_req_subtype ~sub ~super =
  if Config.trace_require_subtype () then
    begin
      Stdio.print_endline "";
      (Sexp.List [
            Sexp.Atom "require_subtype";
            Sexp.List [
              Sexp.Atom "sub";
              sexp_of_uvar (Set.empty (module Int)) sub;
            ];
            Sexp.List [
              Sexp.Atom "super";
              sexp_of_uvar (Set.empty (module Int)) super;
            ];
          ])
      |> Sexp.to_string_hum
      |> Stdio.print_endline;
      Stdio.print_endline ""
    end
and unpack_exist ctx ty = match UnionFind.get ty with
  | `Quant {q_quant  = `Exist; q_var = {bv_id; _}; q_kind = k; q_body = body; _} ->
      subst
        ~target:bv_id
        ~replacement:(fresh_local ctx `Rigid k)
        body
      |> unpack_exist ctx
  | _ ->
      ty
and unroll_quant ctx side q =
  subst
    ~target:q.q_var.bv_id
    ~replacement:(
      fresh_local
        ctx
        (get_flag q.q_quant side)
        q.q_kind
        ~vinfo:q.q_var.bv_info
    )
    q.q_body
and unroll_all_quants ctx side uv = match UnionFind.get uv with
  | `Quant q ->
      unroll_quant ctx side q
      |> unroll_all_quants ctx side
  | _ -> uv
and check_const ctx c ty_want =
  let ty_got = synth_const c in
  require_subtype ctx
    ~sub:ty_got
    ~super:ty_want
    ~reason:(NonEmpty.singleton `Unspecified)
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
  | `Quant q ->
      UnionFind.set
        (`Quant { q with q_body = whnf q.q_body })
        t;
      t
  | `Const(_, `Named `Apply, [f, fk; x, xk], k) ->
      require_kind (UnionFind.make(`Arrow(xk, k))) fk;
      apply_type t f x;
      t
  | _ -> t
and apply_type app f arg =
  match UnionFind.get (whnf f) with
  | `Const(_, `Named `Lambda, [p, _; body, _], _) ->
      let result =
        subst body ~target:(get_id (UnionFind.get p)) ~replacement:arg
      in
      UnionFind.merge (fun _ r -> r) app result;
      ignore (whnf result)
  | _ -> ()
and require_type_eq ctx l r =
  require_subtype ctx ~reason:(NonEmpty.singleton `Unspecified) ~sub:l ~super:r;
  require_subtype ctx ~reason:(NonEmpty.singleton `Unspecified) ~sub:r ~super:l
and join ctx ~reason l r =
  unify ctx
    ~path:(TypePath.base l r)
    ~reason
    (l, `Sub)
    (r, `Sub)


let rec gen_kind = function
  | `Arrow(p, r) -> UnionFind.make (`Arrow(gen_kind p, gen_kind r))
  | `Type -> ktype
  | `Row -> krow
  | `Unknown -> gen_k ()

let typecheck ~get_import_type ~want exp =
  let ctx = make_initial_context ~get_import_type in
  let exp = List.fold_left want ~init:exp ~f:(fun wt_expr (wt_src, wt_type) ->
      DE.WithType {
        wt_src;
        wt_type;
        wt_expr;
      }
    )
  in
  let exp = DE.map exp ~f:gen_kind in
  synth ctx exp

module Tests = struct
  module Helpers = struct
    (*
    let display_type uv =
      sexp_of_uvar (Set.empty (module Int)) uv
      |> Sexp.to_string_hum
      |> Stdio.print_endline
       *)

    let mk_context () = make_initial_context ~get_import_type:(fun _ ->
        failwith "unimplemented"
      )
  end

  open Helpers

  let%test _ =
    (* Right now we are just checking that this doesn't throw an exception
     * (and therefore at least finds a join at all). Ideally we should
     * check that it's the correct one, though at time of writing I(isd)
     * did so manually by inspecting the output of display_type, defined
     * above (to automate we'd actually need to implement equality
     * comparision, which I'm leaving as a TODO). *)
    ignore (
      join (mk_context ())
        ~reason:(NonEmpty.singleton `Unspecified)
        (extend (Label.of_string "A") int (all krow (fun r -> r)))
        (extend (Label.of_string "B") int (all krow (fun r -> r)))
    );
    true

end
