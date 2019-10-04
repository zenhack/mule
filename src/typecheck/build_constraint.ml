open Desugared_ast
open Typecheck_types
open Gensym
open Gen_t
open Common_ast

include Build_constraint_t

let child_g parent child =
  { g_id = gensym ()
  ; g_bound = parent
  ; g_child = child
  }

let with_g: g_node -> (g_node Lazy.t -> u_var) -> g_node =
  fun parent f -> fst
      ( Util.fix
          (child_g (Some{b_ty = `Flex; b_at = parent}))
          (fun g ->
             let root = f g in
             UnionFind.make (`Quant(gen_ty_var (Lazy.force g), root))
          )
      )

let walk_const g c =
  Typebuilder.(
    begin match c with
      | Const.Integer _ -> int
      | Const.Text _ -> text
      | Const.Char _ -> char
    end
    |> at_g g
  )

let rec walk: context -> k_var Expr.t -> u_var =
  fun ({cops; env_types = _; env_terms; g} as ctx) -> function
    | Expr.Const {const_val = c} -> walk_const g c
    | Expr.Embed _ -> Typebuilder.(text |> at_g g)
    | Expr.Var {v_var = v} ->
        let tv = gen_u ktype (`G g) in
        begin match Option.map ~f:Lazy.force (Map.find env_terms v) with
          | None ->
              MuleErr.throw (`UnboundVar v)
          | Some (`Ty tv') ->
              cops.constrain_unify
                (`VarUse
                   (object
                     method bind_type = `Lambda
                     method var = v
                   end)
                )
                tv' tv
          | Some (`G g') ->
              cops.constrain_inst g' tv
        end;
        tv
    | Expr.Lam {l_param = param; l_body = body} ->
        let param_var = gen_u ktype (`G g) in
        let ret_var = gen_u ktype (`G g) in
        let f_var = UnionFind.make (fn (gen_ty_var g) param_var ret_var) in
        let g_body = with_g g
            (fun g -> walk
                { ctx with
                  env_terms = Map.set env_terms ~key:param ~data:(lazy (`Ty param_var));
                  g = Lazy.force g;
                }
                body
            )
        in
        cops.constrain_inst g_body ret_var;
        f_var
    | Expr.Let{let_v = v; let_e = e; let_body = body} ->
        let g_e =
          with_g g (fun g -> walk { ctx with g = Lazy.force g } e)
        in
        walk
          { ctx with env_terms =
                       Map.set env_terms ~key:v ~data:(lazy (`G g_e))
          }
          body
    | Expr.LetRec{letrec_types; letrec_vals; letrec_body} ->
        let record_var = Gensym.anon_var () in
        let get_var_set ls =
          List.map ls ~f:(fun (v, _) -> v)
          |> Set.of_list (module Var)
        in
        let subst_args = Desugared_ast.SubstRec.{
            rec_name = record_var;
            type_vars = get_var_set letrec_types;
            val_vars = get_var_set letrec_types;
          }
        in
        let val_rec =
          List.fold letrec_vals ~init:Expr.EmptyRecord ~f:(fun acc (k, v) ->
              Expr.App {
                app_fn =
                  Expr.App {
                    app_fn = Expr.Update {up_level = `Value; up_lbl = var_to_label k};
                    app_arg = acc;
                  };
                app_arg =
                    Desugared_ast.SubstRec.expr subst_args v;
              }
            )
        in
        let final_rec =
          List.fold letrec_types ~init:val_rec ~f:(fun acc (k, v) ->
              Expr.App {
                app_fn =
                  Expr.App {
                    app_fn = Expr.Update {up_level = `Type; up_lbl = var_to_label k};
                    app_arg = acc;
                  };
                app_arg =
                    Expr.Witness {wi_type = Desugared_ast.SubstRec.typ subst_args v};
              }
            )
        in
        ()
    | Expr.App {app_fn = f; app_arg = arg} ->
        let param_var = gen_u ktype (`G g) in
        let ret_var = gen_u ktype (`G g) in
        let f_var = UnionFind.make(fn (gen_ty_var g) param_var ret_var) in
        let g_f =
          with_g g (fun g -> walk { ctx with g = Lazy.force g} f)
        in
        cops.constrain_inst g_f f_var;
        let g_arg =
          with_g g (fun g -> walk { ctx with g = Lazy.force g } arg)
        in
        cops.constrain_inst g_arg param_var;
        ret_var
    | Expr.EmptyRecord ->
        Typebuilder.(
          all krow (fun r -> record_t ([], Some r))
          |> at_g g
        )
    | Expr.GetField {gf_lbl; _} ->
        Typebuilder.(
          all ktype (fun a -> all krow (fun rt -> (all krow (fun rv ->
              record ([], Some rt) ([gf_lbl, a], Some rv) **> a
            ))))
          |> at_g g
        )
    | Expr.Update { up_level = `Value; up_lbl } ->
        Typebuilder.(
          all ktype (fun a -> all krow (fun rt -> all krow (fun rv ->
                record ([], Some rt) ([], Some rv)
                  **> a
                  **> record ([], Some rt) ([up_lbl, a], Some rv)
            )))
          |> at_g g
        )
    | Expr.Update {
        up_level = `Type;
        up_lbl = lbl;
      } ->
        Typebuilder.(
          all ktype (fun a -> all krow (fun rt -> all krow (fun rv ->
                record ([], Some rt) ([], Some rv)
                  **> witness a
                  **> record ([lbl, a], Some rt) ([], Some rv)
            )))
          |> at_g g
        )
    | Expr.Ctor {c_lbl = lbl; c_arg = param} ->
        let param_var = walk ctx param in
        Typebuilder.(
          all krow (fun r -> union ([lbl, return param_var], Some r))
          |> at_g g
        )
    | Expr.Match {cases; default} when Map.is_empty cases ->
        let term =
          match default with
          | None -> MuleErr.throw `EmptyMatch
          | Some (Some l_param, l_body) ->
              Expr.Lam{l_param; l_body}
          | Some (None, l_body) ->
              Expr.Lam {
                l_param = Var.of_string "_";
                l_body;
              }
        in
        walk ctx term
    | Expr.ConstMatch {cm_cases; cm_default} ->
        let body_ty = gen_u ktype (`G g) in
        let arg_ty = gen_u ktype (`G g) in
        Map.iteri cm_cases ~f:(fun ~key:c ~data:body ->
            let ty = walk ctx body in
            cops.constrain_unify `MatchSiblingsBody ty body_ty;
            cops.constrain_unify `MatchSiblingsPattern (walk_const g c) arg_ty
          );
        let f_ty =
          UnionFind.make (fn (gen_ty_var g) arg_ty body_ty)
        in
        let default_ty = walk ctx cm_default in
        cops.constrain_unify `MatchDefault f_ty default_ty;
        f_ty
    | Expr.Match {cases; default} ->
        let final = match default with
          | None -> UnionFind.make (empty (gen_ty_var g))
          | Some _ -> gen_u krow (`G g)
        in
        let (rowVar, bodyVar) =
          walk_match ctx final (Map.to_alist cases)
        in
        let bound = (get_tyvar (UnionFind.get rowVar)).ty_bound in
        let tv = { ty_id = gensym (); ty_bound = bound } in
        UnionFind.make
          (fn
             (gen_ty_var g)
             (UnionFind.make (union tv rowVar))
             bodyVar)
    | Expr.WithType {wt_type = ty} ->
        Coercions.make_coercion_type ctx ty
    | Expr.Witness {wi_type = ty} ->
        let uty = Coercions.gen_type { ctx; b_at = `G g } `Pos ty in
        UnionFind.make (witness (ty_var_at (`G g)) (Type.get_info ty) uty)
and walk_match ({cops; env_types = _; env_terms; g} as ctx) final =
  List.fold_right
    ~init:(final, gen_u ktype (`G g))
    ~f:(fun (lbl, (var, body)) (row, body') ->
        let ty = gen_u ktype (`G g) in
        let bodyVar =
          walk
            { ctx with
              env_terms = Map.set env_terms ~key:var ~data:(lazy (`Ty ty))
            }
            body
        in
        cops.constrain_unify `MatchSiblingsBody bodyVar body';
        ( UnionFind.make (extend (gen_ty_var g) lbl ty row)
        , bodyVar
        )
      )


let make_cops: unit ->
  ( constraint_ops
    * (unify_edge list) ref
    * ((g_node * u_var list) IntMap.t) ref
    * (Types.reason * k_var * k_var) list ref
  ) = fun () ->
  let ucs = ref [] in (* unification constraints *)
  let ics = ref IntMap.empty in (* instantiation constraints *)
  let kcs = ref [] in (* kind constraints *)
  let cops =
    { constrain_unify   =
        (fun reason l r ->
           ucs := Unify(reason, l, r) :: !ucs)
    ; constrain_inst =
        begin fun g t ->
          ics := Map.update !ics g.g_id ~f:(function
              | None -> (g, [t])
              | Some (_, ts) -> (g, (t :: ts))
            )
        end
    ; constrain_kind =
        (fun rsn l r ->
           kcs := (rsn, l, r) :: !kcs)
    }
  in (cops, ucs, ics, kcs)

let build_constraints: k_var Expr.t -> built_constraints =
  fun expr ->
  let env_terms = Map.map ~f:fst Intrinsics.values in
  let cops, ucs, ics, kcs = make_cops () in
  let (_, ty) = Util.fix
      (child_g None)
      (fun g ->
         let g = Lazy.force g in
         let b_at = `G g in
         let env_types = Map.map Intrinsics.types ~f:(fun ty ->
             let ctx = {
               cops; g; env_types = VarMap.empty; env_terms = VarMap.empty;
             }
             in
             UnionFind.make
               ( `Quant
                   ( ty_var_at b_at
                   , Coercions.gen_type { b_at; ctx } `Pos ty
                   )
               )
           )
         in
         let env_terms = Map.map env_terms ~f:(fun ty ->
             lazy (`G (with_g g (fun g ->
                 let g = Lazy.force g in
                 let b_at = `G g in
                 let ctx = { cops; g; env_types; env_terms = VarMap.empty } in
                 UnionFind.make (
                   `Quant
                     ( ty_var_at b_at
                     , Coercions.gen_type { b_at; ctx } `Pos ty
                     )
                 )))
               )
           )
         in
         let root = walk {cops; env_types; env_terms; g} expr in
         UnionFind.make(`Quant(gen_ty_var g, root))
      )
  in
  { unification = !ucs
  ; instantiation = !ics
  ; kind = !kcs
  ; ty = ty
  }
