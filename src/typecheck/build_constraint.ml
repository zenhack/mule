open Ast.Desugared
open Typecheck_types
open Gensym
open Gen_t

include Build_constraint_t

let child_g parent child =
  { g_id = gensym ()
  ; g_bound = parent
  ; g_child = child
  }

let with_g: g_node -> (g_node Lazy.t -> u_type UnionFind.var) -> g_node =
  fun parent f -> fst (Util.fix (child_g (Some{b_ty = `Flex; b_at = parent})) f)

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
      Coercions.make_coercion_type g ty
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

let make_cops: unit ->
  ( constraint_ops
  * (unify_edge list) ref
  * ((g_node * (u_type UnionFind.var) list) IntMap.t) ref
  ) = fun () ->
  let report = Debug.report Config.dump_constraints in
  let ucs = ref [] in (* unification constraints *)
  let ics = ref IntMap.empty in (* instantiation constraints *)
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
        walk cops VarMap.empty (Lazy.force g) expr
      )
  in
  { unification = !ucs
  ; instantiation = !ics
  ; ty = ty
  }