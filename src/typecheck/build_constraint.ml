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
  fun parent f -> fst
      ( Util.fix
          (child_g (Some{b_ty = `Flex; b_at = parent}))
          (fun g ->
             let root = f g in
             UnionFind.make (`Quant(gen_ty_var (Lazy.force g), root))
          )
      )

let rec walk ~cops ~env_types ~env_terms ~g = function
  | Expr.Integer _ -> UnionFind.make (int (gen_ty_var g))
  | Expr.Text _ -> UnionFind.make (text (gen_ty_var g))
  | Expr.Var v ->
    let tv = gen_u kvar_type (`G g) in
    begin match Lazy.force (Map.find_exn env_terms v) with
      | `Ty tv' ->
        cops.constrain_unify tv' tv
      | `G g' ->
        cops.constrain_inst g' tv
    end;
    tv
  | Expr.Fix _ ->
    (* all a. (a -> a) -> a *)
    let rec ret = lazy (
      let b_at = `Ty ret in
      let a = gen_u kvar_type b_at in
      UnionFind.make
        ( fn
            (gen_ty_var g)
            (UnionFind.make (fn (ty_var_at b_at) a a))
            a
        )
    ) in
    Lazy.force ret
  | Expr.Lam (param, body) ->
    let param_var = gen_u kvar_type (`G g) in
    let ret_var = gen_u kvar_type (`G g) in
    let f_var = UnionFind.make (fn (gen_ty_var g) param_var ret_var) in
    let g_body = with_g g
        (fun g -> walk
            ~cops
            ~env_types
            ~env_terms:(Map.set env_terms ~key:param ~data:(lazy (`Ty param_var)))
            ~g:(Lazy.force g)
            body
        )
    in
    cops.constrain_inst g_body ret_var;
    f_var
  | Expr.Let(v, e, body) ->
    let g_e =
      with_g g (fun g -> walk ~cops ~env_types ~env_terms ~g:(Lazy.force g) e)
    in
    walk
      ~cops
      ~env_types
      ~env_terms:(Map.set env_terms ~key:v ~data:(lazy (`G g_e)))
      ~g
      body
  | Expr.LetType(binds, body) ->
    let env_kinds = Map.map env_types ~f:get_kind in
    let binds = Map.of_alist_exn (module Ast.Var) binds in
    let binds = Map.map binds ~f:(Type.map ~f:gen_k) in
    let u_vars =
      Coercions.gen_types
        cops
        (`G g)
        env_types
        `Pos
        (Map.mapi
           binds
           ~f:(fun ~key ~data ->
               Infer_kind.infer (Map.set env_kinds ~key ~data:(gen_k ())) data
              )
        )
    in
    let env_new =
      Map.merge_skewed env_types u_vars ~combine:(fun ~key:_ _ v -> v)
    in
    walk
      ~cops
      ~env_types:env_new
      ~env_terms
      ~g
      body
  | Expr.App (f, arg) ->
    let param_var = gen_u kvar_type (`G g) in
    let ret_var = gen_u kvar_type (`G g) in
    let f_var = UnionFind.make(fn (gen_ty_var g) param_var ret_var) in
    let g_f =
      with_g g (fun g -> walk ~cops ~env_types ~env_terms ~g:(Lazy.force g) f)
    in
    cops.constrain_inst g_f f_var;
    let g_arg =
      with_g g (fun g -> walk ~cops ~env_types ~env_terms ~g:(Lazy.force g) arg)
    in
    cops.constrain_inst g_arg param_var;
    ret_var
  | Expr.EmptyRecord ->
    UnionFind.make
      (record
         (ty_var_at (`G g))
         (gen_u kvar_row (`G g))
         (UnionFind.make (empty (ty_var_at (`G g))))
      )
  | Expr.GetField (_, lbl) ->
    (* Field accesses have the type:
     *
     * all a r. {lbl: a, ...r} -> a
    *)
    let rec ret = lazy (
      let b_at = `Ty ret in
      let head_var = gen_u kvar_type b_at in
      UnionFind.make
        (fn
           (gen_ty_var g)
           (UnionFind.make
              (record
                 (ty_var_at b_at)
                 (gen_u kvar_row b_at)
                 (UnionFind.make
                    (extend
                       (ty_var_at b_at)
                       lbl
                       head_var
                       (gen_u kvar_row b_at)
                    ))))
           head_var)
    )
    in
    Lazy.force ret
  | Expr.Update (`Value, lbl) ->
    (* Record updates have the type:
     *
     * all a r. {...r} -> a -> {lbl: a, ...r}
    *)
    let rec ret = lazy (
      let b_at = `Ty ret in
      let head_var = gen_u kvar_type b_at in
      let tail_var = gen_u kvar_row b_at in
      let types_row_var = gen_u kvar_row b_at in
      UnionFind.make
        (fn
           (gen_ty_var g)
           (UnionFind.make
              (record
                 (ty_var_at b_at)
                 types_row_var
                 tail_var))
           (UnionFind.make
              (fn
                 (ty_var_at b_at)
                 head_var
                 (UnionFind.make
                    (record
                       (ty_var_at b_at)
                       types_row_var
                       (UnionFind.make
                          (extend
                             (ty_var_at b_at)
                             lbl
                             head_var
                             tail_var
                          )))))))
    ) in
    Lazy.force ret
  | Expr.Update(`Type, lbl) ->
    let rec ret = lazy (
      let b_at = `Ty ret in
      let kvar = gen_k () in
      let head_var = gen_u kvar b_at in
      let tail_var = gen_u kvar_row b_at in
      let vals_row_var = gen_u kvar_row b_at in
      UnionFind.make
        (fn
          (gen_ty_var g)
          (UnionFind.make
             (record
               (ty_var_at b_at)
               tail_var
               vals_row_var))
          (UnionFind.make
             (fn
               (ty_var_at b_at)
               (UnionFind.make (witness (ty_var_at b_at) kvar head_var))
               (UnionFind.make
                  (record
                    (ty_var_at b_at)
                    (UnionFind.make
                       (extend
                         (ty_var_at b_at)
                         lbl
                         head_var
                         tail_var))
                   vals_row_var)))))
    ) in
    Lazy.force ret
  | Expr.Ctor (lbl, param) ->
    let param_var = walk ~cops ~env_types ~env_terms ~g param in
    UnionFind.make
      (union
         (ty_var_at (`G g))
         (UnionFind.make
            (extend
               (ty_var_at (`G g))
               lbl
               param_var
               (gen_u kvar_row (`G g)))
         )
      )
  | Expr.Match {cases; default} when Map.is_empty cases ->
    let term =
      match default with
        | None -> raise (MuleErr.MuleExn EmptyMatch)
        | Some (Some paramVar, body) ->
            Expr.Lam (paramVar, body)
        | Some (None, body) ->
            Expr.Lam (Ast.Var.of_string "_", body)
    in
    walk ~cops ~env_types ~env_terms ~g term
  | Expr.IntMatch {im_cases; im_default} ->
    let body_ty = gen_u kvar_type (`G g) in
    Map.iter im_cases ~f:(fun body ->
        let ty = walk ~cops ~env_types ~env_terms ~g body in
        cops.constrain_unify ty body_ty
      );
    let f_ty = UnionFind.make
        (fn (gen_ty_var g)
           (UnionFind.make (int (gen_ty_var g)))
           body_ty
        )
    in
    let default_ty =
      walk ~cops ~env_types ~env_terms ~g im_default
    in
    cops.constrain_unify f_ty default_ty;
    f_ty
  | Expr.Match {cases; default} ->
    let final = match default with
      | None -> UnionFind.make (empty (gen_ty_var g))
      | Some _ -> gen_u kvar_row (`G g)
    in
    let (rowVar, bodyVar) =
      walk_match ~cops ~env_types ~env_terms ~g final (Map.to_alist cases)
    in
    let bound = (get_tyvar (UnionFind.get rowVar)).ty_bound in
    let tv = { ty_id = gensym (); ty_bound = bound } in
    UnionFind.make
      (fn
         (gen_ty_var g)
         (UnionFind.make (union tv rowVar))
         bodyVar)
  | Expr.WithType ty ->
    let ty = Type.map ty ~f:gen_k in
    Coercions.make_coercion_type env_types g ty cops
  | Expr.Witness ty ->
    let ty = Type.map ty ~f:gen_k in
    let uty = Coercions.gen_type cops (`G g) env_types `Pos ty in
    UnionFind.make (witness (ty_var_at (`G g)) (Type.get_info ty) uty)
and walk_match ~cops ~env_types ~env_terms ~g final = function
  | [] -> (final, gen_u kvar_type (`G g))
  | ((lbl, (var, body)) :: rest) ->
    let ty = gen_u kvar_type (`G g) in
    let bodyVar =
      walk
        ~cops
        ~env_types
        ~env_terms:(Map.set env_terms ~key:var ~data:(lazy (`Ty ty)))
        ~g
        body
    in
    let (row, body') =
      walk_match ~cops ~env_types ~env_terms ~g final rest
    in
    cops.constrain_unify bodyVar body';
    ( UnionFind.make (extend (gen_ty_var g) lbl ty row)
    , bodyVar
    )

let make_cops: unit ->
  ( constraint_ops
    * (unify_edge list) ref
    * ((g_node * (u_type UnionFind.var) list) IntMap.t) ref
  ) = fun () ->
  let ucs = ref [] in (* unification constraints *)
  let ics = ref IntMap.empty in (* instantiation constraints *)
  let cops =
    { constrain_unify   =
        (fun l r ->
           ucs := Unify(l, r) :: !ucs)
    ; constrain_inst =
        begin fun g t ->
          ics := Map.update !ics g.g_id ~f:(function
              | None -> (g, [t])
              | Some (_, ts) -> (g, (t :: ts))
            )
        end
    }
  in (cops, ucs, ics)

let build_constraints: Expr.t -> built_constraints =
  fun expr ->
    let env_terms = Map.map ~f:fst Intrinsics.values in
    let cops, ucs, ics = make_cops () in
    let (_, ty) = Util.fix
        (child_g None)
        (fun g ->
           let g = Lazy.force g in
           let b_at = `G g in
           let env_types = Map.map Intrinsics.types ~f:(fun ty ->
               let ty = Type.map ty ~f:gen_k in
               UnionFind.make
                 ( `Quant
                   ( ty_var_at b_at
                   , Coercions.gen_type
                       cops
                       b_at
                       VarMap.empty
                       `Pos
                       (Infer_kind.infer Intrinsics.kinds ty)
                   )
                 )
             )
           in
           let env_terms = Map.map env_terms ~f:(fun ty ->
               let ty = Type.map ty ~f:gen_k in
               lazy (`G (with_g g (fun g ->
                  let b_at = `G (Lazy.force g) in
                  UnionFind.make (
                    `Quant
                      ( ty_var_at b_at
                      , Coercions.gen_type
                          cops
                          b_at
                          env_types
                          `Pos
                          (Infer_kind.infer Intrinsics.kinds ty)
                      )
                 )))
               )
             )
           in
           let root = walk ~cops ~env_types ~env_terms ~g expr in
           UnionFind.make(`Quant(gen_ty_var g, root))
        )
    in
    { unification = !ucs
    ; instantiation = !ics
    ; ty = ty
    }
