open Ast.Desugared
open Typecheck_types
open Gensym

include Build_constraint_t

let child_g parent child =
  { g_id = gensym ()
  ; g_bound = parent
  ; g_child = child
  }

let with_g: g_node -> (g_node Lazy.t -> u_type UnionFind.var) -> g_node =
  fun parent f -> fst (Util.fix (child_g (Some{b_ty = `Flex; b_at = parent})) f)

let ty_var_at: bound_target -> tyvar = fun b_at ->
  { ty_id = gensym ()
  ; ty_bound = UnionFind.make
    { b_ty = `Flex
    ; b_at = b_at
    }
  }

let tv_pair_at: bound_target -> (tyvar * tyvar) = fun b_at ->
  let x = ty_var_at b_at in
  ( x
  , { ty_id = gensym ()
    ; ty_bound = x.ty_bound
    }
  )

let gen_ty_var: g_node -> tyvar = fun g -> ty_var_at (`G g)


let gen_u: bound_target -> [> `Free of tyvar ] UnionFind.var = fun targ ->
  UnionFind.make (`Free
    { ty_id = gensym ()
    ; ty_bound = UnionFind.make { b_ty = `Flex; b_at = targ }
    })


let rec walk cops env g = function
  | Expr.Var v ->
      let tv = gen_u (`G g) in
      begin match Map.find_exn env v with
        | `Ty tv' ->
            cops.constrain_ty tv' tv
        | `G g' ->
            cops.constrain_inst g' tv
      end;
      tv
  | Expr.Lam (param, body) ->
      let param_var = gen_u (`G g) in
      let ret_var = gen_u (`G g) in
      let f_var = UnionFind.make(`Fn (gen_ty_var g, param_var, ret_var)) in
      let g_body = with_g g
        (fun g -> walk
          cops
          (Map.set env ~key:param ~data:(`Ty param_var))
          (Lazy.force g)
          body
        )
      in
      cops.constrain_inst g_body ret_var;
      f_var
  | Expr.Let(v, e, body) ->
      let g_e = with_g g (fun g -> walk cops env (Lazy.force g) e) in
      walk cops (Map.set env ~key:v ~data:(`G g_e)) g body
  | Expr.App (f, arg) ->
      let param_var = gen_u (`G g) in
      let ret_var = gen_u (`G g) in
      let f_var = UnionFind.make(`Fn (gen_ty_var g, param_var, ret_var)) in
      let g_f = with_g g (fun g -> walk cops env (Lazy.force g) f) in
      cops.constrain_inst g_f f_var;
      let g_arg = with_g g (fun g -> walk cops env (Lazy.force g) arg) in
      cops.constrain_inst g_arg param_var;
      ret_var
  | Expr.EmptyRecord ->
      let tv_rec, tv_row = tv_pair_at (`G g) in
      UnionFind.make (`Record (tv_rec, UnionFind.make (`Empty tv_row)))
  | Expr.GetField lbl ->
      (* Field accesses have the type:
       *
       * all a r. {lbl: a, ...r} -> a
       *)
      let rec ret = lazy (
        let b_at = `Ty ret in
        let head_var = gen_u b_at in
        let tv_rec, tv_row = tv_pair_at b_at in
        UnionFind.make
          (`Fn
            ( gen_ty_var g
            , UnionFind.make
              (`Record
                ( tv_rec
                , UnionFind.make
                  (`Extend
                    ( tv_row
                    , lbl
                    , head_var
                    , gen_u b_at
                    ))))
            , head_var))
      )
      in
      Lazy.force ret
  | Expr.Update lbl ->
      (* Record updates have the type:
       *
       * all a r. {...r} -> a -> {lbl: a, ...r}
       *)
      let rec ret = lazy (
        let b_at = `Ty ret in
        let head_var = gen_u b_at in

        let tv_tail_rec, tv_tail_row = tv_pair_at b_at in
        let tail_var = UnionFind.make (`Free(tv_tail_row)) in

        let tv_rec, tv_row = tv_pair_at b_at in
        UnionFind.make
          (`Fn
            ( gen_ty_var g
            , UnionFind.make
              (`Record (tv_tail_rec, tail_var))
            , UnionFind.make
              (`Fn
                ( ty_var_at b_at
                , head_var
                , UnionFind.make
                  (`Record
                    ( tv_rec
                    , UnionFind.make
                      (`Extend
                        ( tv_row
                        , lbl
                        , head_var
                        , tail_var
                        ))))))))
      ) in
      Lazy.force ret
  | Expr.Ctor (lbl, param) ->
      let tv_union, tv_row = tv_pair_at (`G g) in
      let param_var = walk cops env g param in
      UnionFind.make
        ( `Union
          ( tv_union
          , UnionFind.make
            ( `Extend
                ( tv_row
                , lbl
                , param_var
                , UnionFind.make (`Free (gen_ty_var g))
                )
            )
          )
        )
  | Expr.Match {cases; default} when Map.is_empty cases ->
      begin match default with
        | None -> raise (MuleErr.MuleExn EmptyMatch)
        | Some (Some paramVar, body) ->
            walk cops env g (Expr.Lam (paramVar, body))
        | Some (None, body) ->
            walk cops env g (Expr.Lam (Ast.Var.of_string "_", body))
      end
  | Expr.Match {cases; default} ->
      let final = match default with
        | None -> UnionFind.make (`Empty (gen_ty_var g))
        | Some _ -> UnionFind.make (`Free (gen_ty_var g))
      in
      let (rowVar, bodyVar) = walk_match cops env g final (Map.to_alist cases) in
      let bound = (get_tyvar (UnionFind.get rowVar)).ty_bound in
      let tv = { ty_id = gensym (); ty_bound = bound } in
      UnionFind.make
        ( `Fn
            ( gen_ty_var g
            , UnionFind.make (`Union(tv, rowVar))
            , bodyVar
            )
        )
  | Expr.WithType ty ->
      (* See {MLF-Graph-Infer} section 6. *)
      make_coercion_type cops env g ty
and walk_match cops env g final = function
  | [] -> (final, gen_u (`G g))
  | ((lbl, (var, body)) :: rest) ->
      let ty = gen_u (`G g) in
      let bodyVar = walk cops (Map.set env ~key:var ~data:(`Ty ty)) g body in
      let (row, body') = walk_match cops env g final rest in
      cops.constrain_ty bodyVar body';
      ( UnionFind.make (`Extend(gen_ty_var g, lbl, ty, row))
      , bodyVar
      )
and make_coercion_type cops env g ty =
  (* We construct the type of a coercion as follows:
   *
   * 1. Alpha-rename the existentially-bound variables within the type.
   *    This way we don't have to worry about shadowing in later steps.
   * 2. Collect the names of existentially-bound variables.
   * 3. Generate a unification variable for each existential, and store
   *    them in a map.
   * 4. Walk over the type twice, generating two constraint graphs for it
   *    which share only the nodes for existential variables (looked up
   *    in the map we generated.
   * 5. Make a function node.
   * 6. Bind each of the copies to the function node. The parameter will
   *    be bound rigidly, and the result flexibly.
   * 7. Bind the existentials to the new function node.
   *)
  let rec rename_ex env = function
      (* Alpha-rename existentially bound vars. *)
      | Type.Fn(i, l, r) ->
          Type.Fn(i, rename_ex env l, rename_ex env r)
      | Type.Recur(i, v, body) ->
          Type.Recur(i, v, rename_ex (Map.remove env v) body)
      | Type.Var (i, v) ->
          begin match Map.find env v with
            | Some v' -> Type.Var (i, v')
            | None -> Type.Var (i, v)
          end
      | Type.Record row -> Type.Record (rename_ex_row env row)
      | Type.Union row -> Type.Union (rename_ex_row env row)
      | Type.Quant(i, `All, v, kind, body) ->
          Type.Quant(i, `All, v, kind, rename_ex (Map.remove env v) body)
      | Type.Quant(i, `Exist, v, kind, body) ->
          let v' = Gensym.anon_var () in
          Type.Quant(i, `Exist, v', kind, rename_ex (Map.set ~key:v ~data:v' env) body)
    and rename_ex_row env (i, fields, rest) =
      ( i
      , List.map fields ~f:(fun (l, v) -> (l, rename_ex env v))
      , Option.map rest ~f:(fun r -> match Map.find env r with
            | None -> r
            | Some v -> v
        )
      )
  in
  let merge_disjoint ~key:_ = function
    (* Function to pass to Map.merge, which assumes that the maps are disjoint
     * and just combines the results naively. *)
    | `Left x -> Some x
    | `Right x -> Some x
    | `Both _ -> failwith "impossible"
  in
  let rec collect_exist_vars = function
    (* Collect a list of the existentially bound variables. *)
    | Type.Fn (_, l, r) ->
        Map.merge ~f:merge_disjoint (collect_exist_vars l) (collect_exist_vars r)
    | Type.Recur (_, _, _) ->
        failwith "TODO"
    | Type.Var _ ->
        Map.empty (module Ast.Var)
    | Type.Record row -> collect_exist_row row
    | Type.Union row -> collect_exist_row row
    | Type.Quant (k_var, `Exist, v, _, body) ->
        Map.set ~key:v ~data:k_var (collect_exist_vars body)
    | Type.Quant (_, `All, _, _, body) ->
        collect_exist_vars body
  and collect_exist_row (_, fields, _) =
    List.fold
      fields
      ~init:(Map.empty (module Ast.Var))
      ~f:(fun accum (_, v) ->
          Map.merge ~f:merge_disjoint accum (collect_exist_vars v)
      )
  in
  let rec graph_friendly acc = function
    (* This function addresses a mismatch between syntactic and graphic types:
      * graphic types don't have separate quantifier nodes, nor are quantifiers
      * ordered. Instead, binding edges point at the type node above which the
      * variables would be bound.
      *
      * This function transforms the type ast into a form where there are no
      * Quant nodes, and all variables are collected on type nodes. From there,
      * the graph will be easier to generate.
      *)
    | Type.Quant(_, _, _, Kind.Unknown, _) ->
        failwith "BUG: should have been removed by Kind_infer.infer"
    | Type.Quant(_, _, v, Kind.Type, body) ->
        graph_friendly (`Type v :: acc) body
    | Type.Quant(_, _, v, Kind.Row, body) ->
        graph_friendly (`Row v :: acc) body
    | Type.Fn(_, param, ret) ->
        `Fn(List.rev acc, graph_friendly [] param, graph_friendly [] ret)
    | Type.Recur _ ->
        failwith "TODO"
    | Type.Var (_, v) ->
        `Var (List.rev acc, v)
    | Record row ->
        `Record (List.rev acc, graph_friendly_row row)
    | Union row ->
        `Union (List.rev acc, graph_friendly_row row)
  and graph_friendly_row (_, fields, rest) =
    ( List.map fields ~f:(fun (l, t) -> (l, graph_friendly [] t))
    , rest
    )
  in
  let kinded_ty = Infer_kind.infer (Map.empty (module Ast.Var)) ty in
  let renamed_ty = rename_ex (Map.empty (module Ast.Var)) kinded_ty in
  let exist_vars = collect_exist_vars renamed_ty in
  fst (Util.fix
    (fun vars ->
      let (param_var, ret_var) = Lazy.force vars in
      UnionFind.make
        (`Fn
          ( gen_ty_var g
          , param_var
          , ret_var
          )
        )
    )
    (fun root ->
      (* [root] is the final root of the type; its argument and return values
       * will be the two copies of the type in the annotation, and it will
       * be the bound of the existentials.
       *)
      (* TODO(FIXME?): we have a weird hack in place elsewhere where we bind the
       * scope of record and union types to the root of their row -- do
       * we need to do the same here?
       *)
      let exist_map = Map.map exist_vars ~f:(function
        | `Type -> `Type (gen_u (`Ty root))
        | `Row -> `Row (gen_u (`Ty root))
      ) in
      let _ = (cops, env, exist_map) in
      failwith "TODO"
    )
  )

let make_cops: unit ->
  ( constraint_ops
  * (unify_edge list) ref
  * ((g_node * (u_type UnionFind.var) list) IntMap.t) ref
  ) = fun () ->
  let report = Debug.report Config.dump_constraints in
  let ucs = ref [] in (* unification constraints *)
  let ics = ref (Map.empty (module Int)) in (* instantiation constraints *)
  let cops =
    { constrain_ty   =
      (fun l r ->
        report (fun () -> "constrain types: "
          ^ show_u_type_v l
          ^ " = "
          ^ show_u_type_v r);
        ucs := UnifyTypes(l, r) :: !ucs)
    ; constrain_row  = (fun l r ->
        report (fun () -> "constrain rows: "
            ^ show_u_row_v l
            ^ " = "
            ^ show_u_row_v r);
          ucs := UnifyRows(l, r) :: !ucs)
    ; constrain_inst =
        begin fun g t ->
          report
            (fun () -> "constrain_inst: "
              ^ show_u_type_v t
              ^ " <: "
              ^ show_g g);
          ics := Map.update !ics g.g_id ~f:(function
              | None -> (g, [t])
              | Some (_, ts) -> (g, (t :: ts))
            )
        end
    }
  in (cops, ucs, ics)

let build_constraints: Expr.t -> built_constraints = fun expr ->
  let cops, ucs, ics = make_cops () in
  let (_, ty) = Util.fix
      (child_g None)
      (fun g ->
        walk cops (Map.empty (module Ast.Var)) (Lazy.force g) expr
      )
  in
  { unification = !ucs
  ; instantiation = !ics
  ; ty = ty
  }
