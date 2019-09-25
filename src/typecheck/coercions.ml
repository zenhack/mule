open Ast.Desugared
open Gen_t
open Typecheck_types

open Build_constraint_t

(* Generate coercion types from type annotations.
 *
 * This is based on {MLF-Graph-Infer} section 6, but we do one important
 * thing differently: Instead of *sharing* existential types between the
 * coercion's parameter and result, we map them to flexibly bound bottom
 * nodes in the parameter (as in the paper), but in the result we generate
 * fresh "constant" constructors.
 *
 * The idea is that when we supply a type annotation with an existential
 * in it, we want to *hide* the type from the outside -- this maps closely
 * to sealing in ML module systems. By contrast, the treatment of
 * existentials in the paper is more like "type holes" in some systems --
 * they allow you to specify some of a type annotation, but let the compiler
 * work out the rest. As a concrete example:
 *
 * (fn x. 4) : exist t. t -> t
 *
 * The algorithm in the paper will infer (int -> int), but this code
 * will invent a new constant type t and infer (t -> t).
*)

include Coercions_t

let rec add_row_to_env: u_var VarMap.t -> u_var -> u_var VarMap.t =
  fun env u ->
  match UnionFind.get u with
  | `Const(_, `Named "<empty>", [], _) | `Free _ -> env
  | `Const(_, `Extend lbl, [head, _; tail, _], _) ->
      add_row_to_env
        (Map.set
           env
           ~key:(Ast.var_of_label lbl)
           ~data:head)
        tail
  | _ ->
      failwith "Illegal row"

let rec gen_type
  : type_ctx
    -> sign
    -> k_var Type.t
    -> u_var
  =
  fun ({b_at; ctx = {cops; env_types; env_terms; g = _}} as ctx) sign ty ->
  let tv = ty_var_at b_at in
  match ty with
  | Type.App{app_fn; app_arg; _} ->
      let fn' = gen_type ctx sign app_fn in
      let arg' = gen_type ctx sign app_arg in
      let ret =
        UnionFind.make(apply tv fn' (Type.get_info app_fn) arg' (Type.get_info app_arg))
      in
      cops.constrain_kind
        `AppParamArg
        (get_kind fn')
        (UnionFind.make (`Arrow(get_kind arg', get_kind ret)));
      ret
  | Type.TypeLam{tl_info = k; tl_param = v; tl_body = ty} ->
      let tv = ty_var_at b_at in
      let lam = Gen_t.lambda tv (gen_k ()) (gen_k ()) (fun b_at p ->
          gen_type
            {
              b_at;
              ctx = {
                ctx.ctx
                with env_types = Map.set env_types ~key:v ~data:p
              }
            }
            sign
            ty
        )
      in
      cops.constrain_kind `Lambda (get_kind lam) k;
      lam
  | Type.Opaque _ ->
      MuleErr.bug
        ("Opaque types should have been removed before generating " ^
         "the constraint graph.")
  | Type.Named {n_info = k; n_name = s} ->
      UnionFind.make (`Const(tv, `Named s, [], k))
  | Type.Fn {fn_pvar; fn_param; fn_ret; _} ->
      let param' =
        gen_type ctx (flip_sign sign) fn_param
      in
      cops.constrain_kind (`KnownKind `Fn) (get_kind param') kvar_type;
      let env_terms' = match fn_pvar with
        | Some v ->
            Map.set env_terms ~key:v ~data:(lazy (`Ty param'))
        | None ->
            env_terms
      in
      let ret' =
        gen_type
          { ctx with
            ctx = {
              ctx.ctx with
              env_terms = env_terms';
            }
          }
          sign
          fn_ret
      in
      cops.constrain_kind
        (`Cascade(`KnownKind `Fn, 2))
        (get_kind ret')
        kvar_type;
      UnionFind.make (fn tv param' ret')
  | Type.Recur{mu_var; mu_body; _} ->
      let ret = gen_u kvar_type b_at in
      let ret' =
        gen_type
          { ctx with
            ctx = {
              ctx.ctx
              with env_types = Map.set env_types ~key:mu_var ~data:ret
            }
          }
          sign
          mu_body
      in
      UnionFind.merge (fun _ r -> r) ret ret';
      cops.constrain_kind (`KnownKind `Recur) (get_kind ret') kvar_type;
      ret
  | Type.Var {v_var; _} ->
      begin match Map.find env_types v_var with
        | Some t -> t
        | None -> MuleErr.throw (`UnboundVar v_var)
      end
  | Type.Path{p_var = v; p_lbls = ls; _} ->
      begin match List.rev ls with
        | [] -> Util.find_exn env_types v
        | (l :: ls) ->
            let term = Lazy.force (Util.find_exn env_terms v) in
            let b_at =
              match term with
              | `Ty ty ->
                  !((get_tyvar (UnionFind.get ty)).ty_bound).b_at
              | `G {g_bound = Some bnd; _} ->
                  `G bnd.b_at
              | `G g ->
                  (* I(isd) don't _think_ this should be possible, but in any case
                   * if it is there's only one option: *)
                  `G g
            in
            let tv () = ty_var_at b_at in
            let ret = gen_u (gen_k ()) b_at in
            let init =
              UnionFind.make
                ( record (tv ())
                    (UnionFind.make (extend (ty_var_at b_at) l ret (gen_u kvar_row b_at)))
                    (gen_u kvar_row b_at)
                )
            in
            let record_u = List.fold_left ls ~init ~f:(fun acc l ->
                UnionFind.make
                  (record (tv ())
                     (gen_u kvar_row b_at)
                     (UnionFind.make (extend (tv ()) l acc (gen_u kvar_row b_at))))
              )
            in
            begin match term with
              | `Ty ty ->
                  cops.constrain_unify
                    ( `TypePath
                        (object
                          method bind_type = `Lambda;
                          method var = v;
                          method lbls = List.rev (l :: ls);
                        end)
                    )
                    ty record_u
              | `G g ->
                  cops.constrain_inst g record_u
            end;
            ret
      end
  | Type.Record {r_src = _; r_info = _; r_types; r_values} ->
      let type_row = gen_row ctx sign r_types in
      let env = add_row_to_env env_types type_row in
      UnionFind.make (
        record tv
          type_row
          (gen_row
             { ctx with
               ctx = {
                 ctx.ctx
                 with env_types = env
               }
             }
             sign
             r_values
          )
      )
  | Type.Union {u_row} ->
      UnionFind.make (union tv (gen_row ctx sign u_row))
  | Type.Quant{q_quant = q; q_var = v; q_body = body; _} ->
      let ret = gen_u kvar_type b_at in
      let bound_v =
        UnionFind.make
          (`Free
             ( { ty_id = Gensym.gensym ()
               ; ty_bound = ref
                     { b_ty = get_flag q sign
                     ; b_at = `Ty (lazy ret)
                     }
               }
             , gen_k ()
             ))
      in
      let ret' =
        UnionFind.make
          (`Quant
             ( tv
             , gen_type
                 { b_at = `Ty (lazy ret);
                   ctx = {
                     ctx.ctx
                     with env_types = Map.set env_types ~key:v ~data:bound_v
                   }
                 }
                 sign
                 body
             )
          )
      in
      cops.constrain_kind (`KnownKind `Quant) (get_kind ret') kvar_type;
      UnionFind.merge (fun _ r -> r) ret ret';
      ret
(* [gen_row] is like [gen_type], but for row variables. *)
and gen_row ({ctx = {cops; env_types; _}; b_at} as ctx) sign (_, fields, rest) =
  let rest' =
    match rest with
    | Some v -> Util.find_exn env_types v
    | None -> UnionFind.make (empty (ty_var_at b_at))
  in
  cops.constrain_kind (`KnownKind `Row) (get_kind rest') kvar_row;
  List.fold_right
    fields
    ~init:rest'
    ~f:(fun (lbl, ty) tail ->
        UnionFind.make(
          extend
            (ty_var_at b_at)
            lbl
            (gen_type ctx sign ty)
            tail
        )
      )

let gen_types
  : type_ctx
    -> sign
    -> k_var Type.t VarMap.t
    -> u_var VarMap.t
  =
  fun ({ b_at; ctx = {env_types; _} } as ctx) sign tys ->
  let tmp_uvars = Map.map tys ~f:(fun t -> gen_u (Type.get_info t) b_at) in
  let env' = Map.merge_skewed env_types tmp_uvars ~combine:(fun ~key:_ _ v -> v) in
  let tys = Map.map tys ~f:(
      gen_type { ctx with ctx = { ctx.ctx with env_types = env' } } sign
    )
  in
  Map.iter2 tmp_uvars tys ~f:(fun ~key:_ ~data -> match data with
      | `Both(tmp, final) ->
          UnionFind.merge (fun _ v -> v) tmp final
      | `Left _ | `Right _ ->
          failwith "impossible"
    );
  tys

let make_coercion_type ({g; _} as ctx) ty =
  (* General procedure:
   *
   * 1. Call [gen_type] twice on ty, with different values for [new_exist];
   *    see the discussion at the top of the file.
   * 2. Generate a function node, and bound the two copies of the type to
   *    it, with the parameter rigid, as described in {MLF-Graph-Infer}.
  *)
  fst (Util.fix
         (fun vars ->
            let (param_var, ret_var) = Lazy.force vars in
            UnionFind.make
              ( `Quant
                  ( gen_ty_var g
                  , UnionFind.make (fn (gen_ty_var g) param_var ret_var)
                  )
              )
         )
         (fun root ->
            (* [root] is the final root of the type; it is a quant node, whose child is
             * a function, whose argument and return values will be the two copies of
             * the type in the annotation. The quant node will be the bound of the
             * existentials.
            *)
            let gen sign =
              gen_type { ctx; b_at = `Ty root } sign ty
            in
            (gen `Neg, gen `Pos)
         )
      )
