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
    | `Narrow, sub, `Widen, super
    | `Widen, super, `Narrow, sub ->
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

  let render_u_var uv =
    Debug.start_graph ();
    emit_u_var (ref (Set.empty (module Int))) uv;
    Debug.set_root (get_id (UnionFind.get uv));
    Debug.end_graph()

  let maybe_render_u_var uv =
    if Config.render_constraint_graph () then
      render_u_var uv
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
  | `Narrow -> `Widen
  | `Widen -> `Narrow

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

let subst ~target ~replacement uv =
  (* Nodes we've already seen, to detect cycles and avoid traversing
   * shared sub-graphs: *)
  let seen = ref (Map.empty (module Int)) in
  let rec go uv =
    match UnionFind.get uv with
    | u when get_id u = target -> replacement
    | u when Map.mem !seen (get_id u) -> Util.find_exn !seen (get_id u)
    | `Free _ | `Bound _ -> uv
    | `Quant q when q.q_var.bv_id = target ->
        (* Shadowing the target; stop here. *)
        uv
    | `Quant q -> recurse q.q_id (`Quant { q with q_id = Gensym.gensym () })
    | `Const(old_id, c, args, k) -> recurse old_id (`Const(Gensym.gensym (), c, args, k))
  and recurse old_id result =
    let result_v = UnionFind.make result in
    (* Add an entry to `seen` before recursing, in case we hit
     * ourselves further down. Do this for both the old id and the new one: *)
    seen := Map.set !seen ~key:old_id ~data:result_v;
    seen := Map.set !seen ~key:(get_id result) ~data:result_v;
    UnionFind.set (apply_kids result ~f:go) result_v;
    result_v
  in
  go uv

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

module PushQuants : sig
  val push_down_quants : u_var -> unit
end = struct
  type intcmp = Int.comparator_witness
  type 'v intmap = (int, 'v, intcmp) Map.t
  type intset = (int, intcmp) Set.t

  let make_edge_map: u_var -> intset intmap =
    fun t ->
    let seen = ref (Map.empty (module Int)) in
    let rec go t =
      let id = get_id (UnionFind.get t)  in
      match Map.find !seen id with
      | Some _ -> ()
      | None ->
          begin match UnionFind.get t with
            | `Free _ | `Bound _ ->
                seen := Map.set !seen ~key:id ~data:(Set.empty (module Int))
            | `Quant {q_body; _} ->
                seen := Map.set !seen
                    ~key:id
                    ~data:(Set.singleton (module Int) (get_id (UnionFind.get q_body)));
                go q_body
            | `Const(_, _, args, _) ->
                let kids =
                  List.map args ~f:(fun (t, _k) -> get_id (UnionFind.get t))
                  |> Set.of_list (module Int)
                in
                seen := Map.set !seen ~key:id ~data:kids;
                List.iter args ~f:(fun (t, _k) -> go t)
          end
    in
    go t;
    !seen

  let tsort_edge_map: intset intmap -> int Tsort.result =
    fun edgemap ->
    let edges =
      Map.mapi edgemap ~f:(fun ~key ~data ->
        Set.to_list data
        |> List.map ~f:(fun to_ -> Tsort.{from = key; to_})
      )
      |> Map.data
      |> List.concat
    in
    Tsort.sort
      (module Int)
      ~nodes:(Map.keys edgemap)
      ~edges

  let make_contains_map: u_var -> intset intmap =
    fun uv ->
    let edge_map = make_edge_map uv in
    let sort_res = tsort_edge_map edge_map in
    let contains_map = ref edge_map in
    List.iter sort_res ~f:(
      let collect_descendants from =
        let kids = Map.find_exn edge_map from in
        Set.fold
          kids
          ~init:kids
          ~f:(fun all kid ->
            Set.union all (Map.find_exn !contains_map kid)
          )
      in
      function
      | `Single from ->
          contains_map := Map.set
              !contains_map
              ~key:from
              ~data:(collect_descendants from)
      | `Cycle (f, fs) ->
          let froms = f :: fs in
          let descendants =
            List.fold
              froms
              ~init:(Set.of_list (module Int) froms)
              ~f:(fun all from ->
                Set.union all (collect_descendants from)
              )
          in
          List.iter froms ~f:(fun from ->
            contains_map := Map.set !contains_map ~key:from ~data:descendants
          )
    );
    !contains_map

  let subtree_contains cmap q uv =
    let id = get_id (UnionFind.get uv) in
    let contains = Util.find_exn cmap id in
    id = q.q_var.bv_id || Set.mem contains q.q_var.bv_id


  let push_down_quants cmap uv =
    let seen = ref (Set.empty (module Int)) in
    let rec actual_push q uv =
      let u = UnionFind.get uv in
      match u with
      | `Free _ -> ()
      | `Bound bv ->
          (* Insert the quantifier right above this node: *)
          UnionFind.set
            (`Quant { q with q_body = UnionFind.make (`Bound bv) })
            uv
      | `Quant q' ->
          if Poly.equal q.q_quant q'.q_quant then
            begin
              actual_push q q'.q_body
            end
          else
            (* If the quantifiers are unequal, we have to stop, as flipping
             * them would be unsound. *)
            UnionFind.set
              (`Quant { q with q_body = UnionFind.make u })
              uv
      | `Const (_, c, args, _) ->
          (* Check which branches contain our variable.
           * - If it is exactly one, we descend into that branch. If that
           *   branch is the parameter to a function, we flip the quantifier.
           * - If it is more than one, we stop here, and wrap this node in
           *   the quantifier.
           * - We shouldn't get here if it is zero because of optimizations
           *   elsewhere, but if so we just drop the quantifier and do
           *   nothing
          *)
          let xs =
            List.filter_mapi args ~f:(fun i (uv, _) ->
              if subtree_contains cmap q uv then
                Some(i, uv)
              else
                None
            )
          in
          match c, xs with
          | `Named `Fn, [0, uv] ->
              (* Flip the quantifier for contravariance: *)
              actual_push
                { q with q_quant = flip_quant q.q_quant }
                uv
          | _, [_, uv] ->
              actual_push q uv
          | _, (_::_) ->
              UnionFind.set
                (`Quant { q with q_body = UnionFind.make u })
                uv
          | _, [] -> ()
    in
    let rec go uv =
      let u = UnionFind.get uv in
      if not (Set.mem !seen (get_id u)) then
        begin
          seen := Set.add !seen (get_id u);
          match u with
          | `Free _ | `Bound _ -> ()
          | `Const (_, _, args, _) ->
              List.iter args ~f:(fun (uv, _k) -> go uv)
          | `Quant q ->
              go q.q_body;
              begin
                if subtree_contains cmap q q.q_body then
                  (* Optimization: we only need to do this if the body actually contains
                   * the variable; otherwise we can just drop the quantifier entirely. *)
                  actual_push q q.q_body
              end;
              UnionFind.merge (fun _ r -> r) uv q.q_body
        end
    in
    go uv

  let push_down_quants uv =
    push_down_quants (make_contains_map uv) uv
end

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
  let res =
    List.fold to_generalize ~init:result ~f:(fun acc f -> f acc)
  in
  PushQuants.push_down_quants res;
  res

(* Create a new local with the given flag and kind. *)
let fresh_local ?(vinfo={vi_ident = `Unknown; vi_binder = None}) ctx ty_flag k =
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
  let (new_check, new_synth) =
    List.partition_map rec_vals ~f:(fun (v, ty, e) ->
      match ty with
      | Some ty -> `Fst(v, make_type ctx ty, e)
      | None -> `Snd
            ( v
            , fresh_local ctx `Flex ktype ~vinfo:{
                vi_ident = `RecBindVal(v, DE.get_src_expr e);
                vi_binder = None;
              }
            , e
            )
    )
  in
  (* NOTE: the order in which we concatenate these is *VERY IMPORTANT*.
   * The un-annoated ones have to come first, because, if we check the
   * annotated ones first, the process may instantiate the unsolved
   * variables for the un-annotated ones with temporary rigid variables,
   * causing spurrious failures. This is essentially the same problem
   * that caused #22, but in a different place. *)
  let new_vars = new_synth @ new_check in
  let ctx' =
    List.fold new_vars ~init:ctx ~f:(fun ctx (vname, v, _) ->
      { ctx with vals_env = Map.set ctx.vals_env ~key:vname ~data:v }
    )
  in
  let checked_vals =
    List.map new_vars ~f:(fun (v, ty, e) ->
      ignore (
        with_locals ctx' (fun ctx ->
          check ctx e ty ~reason:(NonEmpty.singleton `Unspecified)
        )
      );
      (v, unpack_exist ctx ty)
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
      quant ~ident:(`VarName (Var.to_string q_var)) q_quant (gen_k ()) (fun v ->
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
      let t = recur ~ident:(`VarName (Var.to_string mu_var)) (fun v ->
          make_type
            { ctx with type_env = Map.set ctx.type_env ~key:mu_var ~data:v }
            mu_body
        )
      in
      require_kind (get_kind t) ktype;
      t
  | DT.TypeLam{tl_param; tl_body; _} ->
      lambda ~ident:(`VarName (Var.to_string tl_param)) (gen_k ()) (fun p ->
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
          ~init:(exist ~ident:`Unknown krow (fun rv -> (exist ~ident:`Unknown krow (fun rt ->
              record (extend last result_type rt) rv
            ))))
          ~f:(fun tail next ->
            exist ~ident:`Unknown krow (fun rv -> (exist ~ident:`Unknown krow (fun rt ->
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
    | None, `Record `Type -> empty_record_types
    | None, `Union -> empty_union
    | None, `Record `Value -> empty_record_vals
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
    | DE.Lam{l_param; l_body; l_src = _} ->
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
                ~reason:(NonEmpty.singleton (
                    `RecordUpdate(uv_lbl, uv_record, `Val(uv_val))
                  )));
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
              ~reason:(NonEmpty.singleton (
                  `RecordUpdate (ut_lbl, ut_record, `Type(ut_type))
                ))
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
            let rec_vals =
              List.map r.rec_vals ~f:(fun (v, _, e) -> (v, e))
            in
            record
              (build_row ctx.type_env (List.concat r.rec_types) empty_record_types)
              (build_row ctx.vals_env rec_vals empty_record_vals)
          )
        )
    | DE.Ctor{c_lbl; c_arg} ->
        let arg_t = synth ctx c_arg in
        union (extend c_lbl arg_t empty_union)
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
    | DE.Match {m_branch; _}->
        with_locals ctx (fun ctx ->
          let (p, r) = synth_branch ctx m_branch in
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
  Graphviz.maybe_render_u_var result;
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
            | None when have_default -> (some_union, result)
            | None -> (empty_union, result)
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
  Graphviz.maybe_render_u_var ty_want;
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
      let p = fresh_local ctx `Flex ktype in
      ignore
        (check ctx
            app_fn
            (p **> ty_want)
            ~reason:(NonEmpty.cons (`ApplyFn(app_fn, app_arg, p)) reason));
      ignore
        (check ctx
            app_arg
            p
            ~reason:(NonEmpty.cons (`ApplyArg(app_fn, app_arg, ty_want)) reason));
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
  | DE.Lam{l_param; l_body; l_src = _} ->
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
  | DE.Match {m_branch; _} ->
      with_locals ctx (fun ctx ->
        check_maybe_flex ctx e ty_want ~f:(fun want -> match UnionFind.get want with
          | `Const(_, `Named `Fn, [p, _; r, _], _) ->
              check_branch ctx m_branch (p, r)
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
  let want = unroll_all_quants ctx `Widen (whnf ty_want) in
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
      ~init:( empty_record_types
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
      ~init:( empty_record_vals
            , Map.empty (module Var)
            , ctx
      )
      ~f:(fun (row, exp_map, ctx) (v, ty, e) ->
        let tyvar = match ty with
          | None -> fresh_local ctx `Flex ktype
          | Some ty -> make_type ctx ty |> with_kind ktype
        in
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
      | None when have_default -> some_union
      | None -> empty_union
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
      (sub, `Narrow)
      (super, `Widen)
  )
and unify =
  fun ctx ~reason (sub, sub_dir) (super, super_dir) ->
  (* Normalize the order of the directions, so we never have to deal with
   * (`Widen, `Narrow), which is symmetric to (`Narrow, `Widen) *)
  match sub_dir, super_dir with
  | `Widen, `Narrow ->
      unify ctx ~reason (super, super_dir) (sub, sub_dir)
  | _ ->
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
    -> (u_var * unify_dir)
    -> (u_var * unify_dir)
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

        | `Bound {bv_info = { vi_binder = Some `Rec; vi_ident = `VarName var }; _}, _
        | _, `Bound {bv_info = { vi_binder = Some `Rec; vi_ident = `VarName var }; _} ->
            (* This can happen if the user supplies the type `rec a. a`. Normally,
             * the rec-bound variable gets replaced with the body but if the variable
             * is ungarded like that it sticks around. *)
            MuleErr.throw
              (`TypeError
                  (`UnguardedRecursiveType
                      ("rec " ^ var ^ ". " ^ var)))
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

        (* If we see a quantifier, we "unroll" it, introducing an unknown
           variable, and then try to unify with the resulting body. *)
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

        (* Unifying two distinct rigid variables should fail. If we hit rigid variables
           here we know they are distinct, because if they were the same already, they
           would have been covered above: *)
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

        (* Unions *)
        | `Const(_, `Named `Union, [row_sub, _], _),
          `Const(_, `Named `Union, [row_super, _], _) ->
            union (
              unify_union ctx
                ~reason
                ~path:(TypePath.append path `UnionRow)
                (row_sub, sub_dir)
                (row_super, super_dir)
            )
        | `Const(_, `Named `Union, x, _), `Const(_, `Named `Union, y, _) ->
            wrong_num_args `Union 1 x y

        (* Records *)
        | `Const(_, `Named `Record, [rtype_sub, _; rvals_sub, _], _),
          `Const(_, `Named `Record, [rtype_super, _; rvals_super, _], _) ->
            unify_record ctx
              (rtype_sub, rvals_sub, sub_dir)
              (rtype_super, rvals_super, super_dir)
              ~reason
              ~path
        | `Const(_, `Named `Record, x, _), `Const(_, `Named `Record, y, _) ->
            wrong_num_args `Record 2 x y

        | `Const(_, `Extend _, _, _), `Const(_, `Extend _, _, _) ->
            unify_extend ctx
              ~reason
              ~path
              (sub, sub_dir)
              (super, super_dir)

        (* Type-level lambdas *)
        | `Const(_, `Named `Lambda, [pl, kpl; bl, kbl], _),
          `Const(_, `Named `Lambda, [pr, kpr; br, kbr], _) ->
            require_kind kpl kpr;
            require_kind kbl kbr;
            (* Substitue the same rigid variable for both lambdas'
             * parameters, and then check the bodies.
             *
             * TODO(error messages): we should probably annotate the variables
             * so we can track them back to lambda parameters.
            *)
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
            lambda ~ident:`Unknown (get_kind p) (fun p' ->
              subst
                ~target:(get_id (UnionFind.get p))
                ~replacement:p'
                body
            )

        (* Type-level function application. We should only get here if
           the functions are opaque (variables), since otherwise this
           isn't in whnf. TODO: add a sanity check?
        *)
        | `Const(_, `Named `Apply, [fl, flk; argl, arglk], retlk),
          `Const(_, `Named `Apply, [fr, frk; argr, argrk], retrk) ->
            require_kind flk frk;
            require_kind arglk argrk;
            require_kind retlk retrk;
            require_type_eq ctx fl fr;
            require_type_eq ctx argl argr;
            apply fl argl

        (* Something else, should be impossible. TODO: it would be nice to refactor all
           this so that we don't need a catchall panic; this defeats static exauhstiveness
           checking, but unfortunately right now there are a bunch of "can't happen" cases
           that depend on higher-level logic not captured by the types, or things that are
           actually covered, but are handled by by guards (e.g. `Const, `Const where the
           ctors are different), and it would be rather tedious to enumerate all of them
           as-is in a way the exhaustiveness checker can understand. *)
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
and unify_union ctx ~path ~reason sub super =
  unify ctx ~path ~reason sub super
and unify_record ctx ~path ~reason
    (rtype_sub, rvals_sub, sub_dir)
    (rtype_super, rvals_super, super_dir)
  =
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
and unify_extend ctx ~path ~reason (sub, sub_dir) (super, super_dir) =
  (* Unify two rows that start with an `Extend. *)
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
    (* Merge a row containing the label [lbl] with another row
       not containing that label.

       parameters:

       - [path] is the path into the type, for assisting with error
         messages.
       - tailref is a reference containing the row without [lbl]. It
         will be updated with the result of unification.
       - taildir is the direction of the row without [lbl].
       - [lbl] is the label we're interested in.
       - [lbldir] is the direction of the row including [lbl].
       - [ty] is the field for [lbl] in the row that contains it.
         We accept a tuple [(ty, _kind)] for convienence at the
         call site, but [_kind] is unused.
    *)
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
  unfold_row merged tail
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
  | `Quant {q_quant  = `Exist; q_var = {bv_id; bv_info; _}; q_kind = k; q_body = body; _} ->
      subst
        ~target:bv_id
        ~replacement:(fresh_local ctx `Rigid k ~vinfo:bv_info)
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
    (l, `Narrow)
    (r, `Narrow)
and fold_row row =
  (* Fold a row (`Const(_, `Extend _, [_; `Const(_, `Extend _, ..., _), _], _))
     into a pair (fields, tail). `fields` is a map from labels to the fields,
     tail is the first item in the chain that is not (`Const(_, `Extend _, ...)).
  *)
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
  go (Map.empty (module Label)) row
and unfold_row fields tail =
  (* Inverse of fold_row *)
  Map.fold
    fields
    ~init:tail
    ~f:(fun ~key ~data tail -> extend key data tail)


let rec gen_kind = function
  | `Arrow(p, r) -> UnionFind.make (`Arrow(gen_kind p, gen_kind r))
  | `Type -> ktype
  | `Row -> krow
  | `Unknown -> gen_k ()

let typecheck ~get_import_type ~want ~export exp =
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
  let ty = synth ctx exp in
  if export then
    unpack_exist ctx ty
  else
    ty

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
        (extend (Label.of_string "A") int empty_union)
        (extend (Label.of_string "B") int empty_union)
    );
    true

end
