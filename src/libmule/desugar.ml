open Common_ast
module SP = Surface_ast.Pattern
module SC = Surface_ast
module S = Surface_ast.Expr
module ST = Surface_ast.Type
module D = Desugared_ast.Expr
module Ast = Common_ast
module C = Common_ast.Const
module DT = Desugared_ast.Type
module DK = Desugared_ast.Kind

let incomplete_pattern () =
  MuleErr.throw `IncompletePattern

let unreachable_cases cases =
  MuleErr.throw (`UnreachableCases cases)

(* [substitute_type_apps f params ty] replaces occurances of [f] applied to
 * the list of parameters in [ty] with just [f]. *)
let substitue_type_apps: Ast.Var.t -> Ast.Var.t list -> DK.maybe_kind DT.t -> DK.maybe_kind DT.t =
  fun fvar params ->
  let vars = Set.of_list (module Ast.Var) (fvar :: params) in
  let rec make_var_list acc = function
    | DT.App {
        app_fn;
        app_arg = DT.Var {v_var; _};
        _;
      } -> make_var_list (v_var :: acc) app_fn
    | DT.Var{v_var; _} -> Some (v_var :: acc)
    | _ -> None
  in
  let make_var_list = make_var_list [] in
  let bound_var = function
    (* If the argument would bound a variable inside it, return [Some var], otherwise [None]. *)
    | DT.Quant{q_var; _} -> Some q_var
    | DT.Recur{mu_var; _} -> Some mu_var
    | DT.Fn{fn_pvar = Some v; _} -> Some v
    | DT.TypeLam {tl_param; _} -> Some tl_param
    | DT.Fn _
    | DT.App _
    | DT.Opaque _
    | DT.Var _
    | DT.Record _
    | DT.Union _
    | DT.Path _
    | DT.Named _
      -> None
  in
  (* Return whether one of the variables in [vars] would be shadowed in part of [ty]. *)
  let shadows_var ty =
    match bound_var ty with
    | None -> false
    | Some v -> Set.mem vars v
  in
  let rec go: DK.maybe_kind DT.t -> DK.maybe_kind DT.t = fun ty ->
    if Poly.equal (Some (fvar::params)) (make_var_list ty) then
      DT.Var {v_var = fvar; v_info = `Unknown}
    else if shadows_var ty then
      begin match ty with
        (* If any of the variables are shadowed, we can return immediately.
         *
         * _HOWEVER_, we need to treat functions specially, since they if they
         * shadow a variable they *only* shadow it in the return value; we still
         * need to recurse on the parameter. This is a little gross.
        *)
        | DT.Fn{fn_info; fn_pvar; fn_param; fn_ret} ->
            DT.Fn {fn_info; fn_pvar; fn_param = go fn_param; fn_ret}
        | _ ->
            ty
      end
    else
      begin match ty with
        | DT.Quant{q_info; q_quant; q_var; q_body} ->
            DT.Quant{
              q_info;
              q_quant;
              q_var;
              q_body = go q_body;
            }
        | DT.Recur{mu_info; mu_var = v; mu_body = body} ->
            DT.Recur{mu_info; mu_var = v; mu_body = go body}
        | DT.Fn{fn_info; fn_pvar; fn_param = p; fn_ret = r} ->
            DT.Fn {
              fn_info;
              fn_pvar;
              fn_param = go p;
              fn_ret = go r;
            }
        | DT.App{app_info; app_fn = f; app_arg = x} ->
            DT.App{app_info; app_fn = go f; app_arg = go x}
        | DT.Union{u_row} ->
            DT.Union{u_row = go_row u_row}
        | DT.Record{r_info; r_types; r_values; r_src} ->
            DT.Record {
              r_info;
              r_types = go_row r_types;
              r_values = go_row r_values;
              r_src;
            }
        | DT.Opaque _ | DT.Named _ | DT.Var _ | DT.Path _ -> ty
        | DT.TypeLam{tl_info; tl_param; tl_body} ->
            DT.TypeLam {
              tl_info;
              tl_param;
              tl_body = go tl_body;
            }
      end
  and go_row {row_info; row_fields; row_rest} =
    { row_info
    ; row_fields = List.map row_fields ~f:(fun (lbl, t) -> (lbl, go t))
    ; row_rest
    }
  in
  go

let rec quantify_opaques t = match t with
  (* Transform opaque type members into existentials, e.g.
   *
   * { type t }
   *
   * becomes:
   *
   * exist a. { type t = a }
  *)
  | DT.Named _ | DT.Path _ | DT.Var _ -> t
  | DT.App{app_info; app_fn; app_arg} ->
      DT.App {
        app_info;
        app_fn = quantify_opaques app_fn;
        app_arg = quantify_opaques app_arg;
      }
  | DT.TypeLam{tl_info; tl_param; tl_body} ->
      DT.TypeLam{tl_info; tl_param; tl_body = quantify_opaques tl_body}
  | DT.Record {r_src; r_info; r_types = {row_info; row_fields; row_rest}; r_values} ->
      let vars = ref [] in
      let row_fields = List.map row_fields ~f:(fun (lbl, ty) ->
          match quantify_opaques ty with
          | DT.Opaque {o_info} ->
              let var = Gensym.anon_var () in
              vars := (lbl, var) :: !vars;
              (lbl, DT.Var { v_info = o_info; v_var = var })
          | ty' -> (lbl, ty')
        )
      in
      let init =
        DT.Record
          { r_info
          ; r_src
          ; r_types = {row_info; row_fields; row_rest}
          ; r_values = quantify_row_opaques r_values
          }
      in
      List.fold !vars ~init ~f:(fun ty (lbl, v) ->
        DT.Quant {
          q_info = `Unknown;
          q_quant = `Exist;
          q_var = v;
          q_body =
            DT.subst
              (var_of_label lbl)
              (DT.Var {v_var = v; v_info = `Unknown})
              ty
        }
      )
  | DT.Opaque i -> DT.Opaque i
  | DT.Fn {fn_info; fn_pvar; fn_param; fn_ret} ->
      DT.Fn {
        fn_info;
        fn_pvar;
        fn_param = quantify_opaques fn_param;
        fn_ret = quantify_opaques fn_ret;
      }
  | DT.Recur {mu_info; mu_var; mu_body} ->
      DT.Recur{mu_info; mu_var; mu_body = quantify_opaques mu_body}
  | DT.Union {u_row} -> DT.Union { u_row = quantify_row_opaques u_row }
  | DT.Quant{q_info; q_quant; q_var; q_body} ->
      DT.Quant{q_info; q_quant; q_var; q_body = quantify_opaques q_body}
and quantify_row_opaques {row_info; row_fields; row_rest} =
  { row_info
  ; row_fields = List.map
      row_fields
      ~f:(fun (lbl, ty) -> (lbl, quantify_opaques ty))
  ; row_rest
  }

let rec desugar_type' ty = match ty.Loc.l_value with
  | ST.Import _ ->
      failwith "TODO: implememnt import type"
  | ST.Fn{
      fn_param = Loc.{l_value = ST.Annotated{anno_var; anno_ty = param; _}; _};
      fn_ret;
      _;
    } ->
      DT.Fn {
        fn_info = `Type;
        fn_pvar = Some anno_var.Loc.l_value;
        fn_param = desugar_type' param;
        fn_ret = desugar_type' fn_ret;
      }
  | ST.Fn{fn_param = param; fn_ret = ret; _} ->
      DT.Fn {
        fn_info = `Type;
        fn_pvar = None;
        fn_param = desugar_type' param;
        fn_ret = desugar_type' ret;
      }
  | ST.Quant{q_quant = q; q_vars = vs; q_body = body; _} ->
      List.fold_right
        vs
        ~init:(desugar_type' body)
        ~f:(fun v body -> DT.Quant {
            q_info = `Type;
            q_quant = q.Loc.l_value;
            q_var = v.Loc.l_value;
            q_body = body;
          }
        )
  | ST.Recur{recur_var = v; recur_body = body; _} ->
      DT.Recur {
        mu_info = `Type;
        mu_var = v.Loc.l_value ;
        mu_body = desugar_type' body;
      }
  | ST.Var {v_var = v; _} ->
      DT.Var{v_info = `Unknown; v_var = v.Loc.l_value}
  | ST.Union {u_l; u_r; _} ->
      DT.Union {u_row = desugar_union_type None (u_l, u_r) }
  | ST.Record {r_items = r; _} ->
      desugar_record_type [] [] r (Some ty)
  | ST.App{app_fn = Loc.{l_value = ST.Ctor{c_lbl; _}; _}; app_arg = t; _} ->
      DT.Union {
        u_row = {
          row_info = `Type;
          row_fields = [(c_lbl.Loc.l_value, desugar_type' t)];
          row_rest = None;
        };
      }
  | ST.RowRest {rr_var = v; _} ->
      DT.Union {
        u_row = {
          row_info = `Type;
          row_fields = [];
          row_rest = Some v.Loc.l_value;
        };
      }
  | ST.Annotated _ ->
      MuleErr.throw (`IllegalAnnotatedType ty.Loc.l_value)
  | ST.Path{p_var; p_lbls; _} ->
      DT.Path {
        p_info = `Unknown;
        p_var = p_var.Loc.l_value;
        p_lbls = List.map p_lbls ~f:(fun Loc.{l_value = l; _} -> l)
      }
  | ST.App{app_fn = f; app_arg = x; _} ->
      DT.App {
        app_info = `Unknown;
        app_fn = desugar_type' f;
        app_arg = desugar_type' x;
      }
  | ST.Ctor _ ->
      MuleErr.bug "ctors should be applied."
and desugar_union_type tail (l, r) =
  match desugar_type' l, desugar_type' r, tail with
  | DT.Union{u_row = {row_fields = lbls_l; row_rest = None; _}},
    DT.Union{u_row = {row_fields = lbls_r; row_rest = None; _}},
    (Some v)
  | DT.Union{u_row = {row_fields = lbls_l; row_rest = None; _}},
    DT.Union{u_row = {row_fields = lbls_r; row_rest = Some v; _}},
    None
  | DT.Union{u_row = {row_fields = lbls_l; row_rest = Some v; _}},
    DT.Union{u_row = {row_fields = lbls_r; row_rest = None; _}},
    None ->
      {row_info = `Type; row_fields = lbls_l @ lbls_r; row_rest = Some v}
  | DT.Union{u_row = {row_fields = lbls_l; row_rest = None; _}},
    DT.Union{u_row = {row_fields = lbls_r; row_rest = None; _}},
    None ->
      {row_info = `Type; row_fields = lbls_l @ lbls_r; row_rest = None}
  | _ ->
      MuleErr.throw
        (`MalformedType
            "Unions must be composed of ctors and at most one ...r")
and desugar_record_type types fields r r_src =
  let rec go types fields = function
    (* TODO: how do we have variable fields for the type row? *)
    | (ST.Type(lbl, params, Some t) :: fs) ->
        let (_, ty) = desugar_type_binding (SC.var_of_label lbl, params, t) in
        go ((lbl.Loc.l_value, ty)::types) fields fs
    | (ST.Type(lbl, params, None) :: fs) ->
        let kind =
          List.fold
            params
            ~init:`Unknown
            ~f:(fun k _ -> `Arrow(`Unknown, k))
        in
        go ((lbl.Loc.l_value, DT.Opaque {o_info = kind})::types) fields fs
    | [] ->
        DT.Record
          { r_src
          ; r_info = `Type
          ; r_types = {row_info = `Row; row_fields = types; row_rest = None}
          ; r_values = {row_info = `Row; row_fields = fields; row_rest = None}
          }
    | [ST.Rest v] ->
        DT.Record
          { r_src
          ; r_info = `Type
          ; r_types = {row_info = `Row; row_fields = types; row_rest = None}
          ; r_values = {row_info = `Row; row_fields = fields; row_rest = Some v.Loc.l_value}
          }
    | (ST.Field (l, t) :: rest) ->
        go types ((l.Loc.l_value, desugar_type' t)::fields) rest
    | (ST.Rest _ :: _) ->
        MuleErr.throw
          (`MalformedType "row variable before the end of a record type.")
  in
  go types fields (List.map r ~f:(fun {l_value = l; _} -> l))
and desugar_type t =
  desugar_type' t
  |> quantify_opaques
and desugar Loc.{l_value = e; _} = match e with
  | S.Import _ -> failwith "TODO: implement import"
  | S.Embed {e_path; e_from; _} ->
      D.Embed {
        e_path;
        e_value = Lwt_main.run (Paths.resolve_embed ~here:e_from ~target:e_path);
      }
  | S.Const {const_val = c; _} -> D.Const {const_val = c}
  | S.Var {v_var = v; _} -> D.Var {v_var = v.Loc.l_value}
  | S.App{app_fn = f; app_arg = x; _} -> D.App {
      app_fn = desugar f;
      app_arg = desugar x;
    }
  | S.Lam{lam_params; lam_body; _} -> desugar_lambda lam_params lam_body
  | S.Record {r_fields = []; _} -> D.EmptyRecord
  | S.Record {r_fields = fields; _} -> desugar_record fields
  | S.Update{up_arg; up_fields; _} -> desugar_update up_arg up_fields
  | S.GetField {gf_arg = e; gf_lbl = l; _} ->
      D.App {
        app_fn = D.GetField {
            gf_lbl = l.Loc.l_value;
          };
        app_arg = desugar e;
      }
  | S.Ctor {c_lbl = label; _} ->
      (* The choice of variable name here doesn't matter, since
       * there's nothing we need to worry about shadowing. *)
      let l_param = Ast.Var.of_string "x" in
      D.Lam {
        l_param;
        l_body = D.Ctor {
            c_lbl = label.Loc.l_value;
            c_arg = D.Var {v_var = l_param };
          };
      }
  | S.Match {match_arg = e; match_cases = cases; _} ->
      D.App {
        app_fn = desugar_match cases;
        app_arg = desugar e;
      }
  | S.WithType{wt_term = e; wt_type = ty; _} ->
      D.WithType {
        wt_expr = desugar e;
        wt_type = desugar_type ty;
      }
  | S.Let {
      let_binds = bindings;
      let_body = body;
      _;
    } ->
      desugar_let bindings body
and desugar_update e fields =
  let rec go e = function
  | [] -> desugar e
  | `Value (l, _, v) :: fs ->
      D.App {
        app_fn = D.App {
            app_fn = D.UpdateVal {
                uv_lbl = l.Loc.l_value;
              };
            app_arg = go e fs
          };
        app_arg = desugar v;
      }
  | `Type (lbl, params, ty) :: fs ->
      let (_, ty) = desugar_type_binding (SC.var_of_label lbl, params, ty) in
      D.UpdateType {
        ut_lbl = lbl.Loc.l_value;
        ut_type = ty;
        ut_record = go e fs;
      }
  in
  go e (List.map fields ~f:(fun Loc.{l_value = v; _} -> v))
and desugar_lambda ps body =
  let rec go = function
    | [] -> desugar body
    | (SP.Var {v_var; v_type = None; _} :: pats) ->
        D.Lam {l_param = v_var.Loc.l_value; l_body = go pats}
    | (SP.Wild :: pats) ->
        D.Lam {
          l_param = Gensym.anon_var ();
          l_body = go pats;
        }
    | (SP.Var {v_var; v_type = Some ty; _} :: pats) ->
        let v_var = v_var.Loc.l_value in
        D.Lam {
          l_param = v_var;
          l_body = D.Let {
              let_v = v_var;
              let_e =
                D.WithType {
                  wt_expr = D.Var {v_var};
                  wt_type = desugar_type ty;
                };
              let_body = go pats;
            };
        }
    | ((SP.Const _) :: _) -> incomplete_pattern ()
    | (SP.Ctor{c_lbl; c_arg; _} :: pats) ->
        let v = Gensym.anon_var () in
        D.Match {
          default = None;
          cases = LabelMap.singleton
              c_lbl.Loc.l_value
              ( v
              , D.App {
                  app_fn = go (c_arg.Loc.l_value :: pats);
                  app_arg = D.Var {v_var = v}
                }
              )
        }
  in
  go (List.map ps ~f:(fun p -> p.Loc.l_value))
and desugar_record fields =
  let types, values =
    List.fold_right fields ~init:([], []) ~f:(fun bind (types, values) ->
      match bind.Loc.l_value with
      | `Value(l, None, e) -> (types, ((Ast.var_of_label l.Loc.l_value, desugar e) :: values))
      | `Value(l, Some ty, e) ->
          ( types
          , ( Ast.var_of_label l.Loc.l_value
            , D.WithType {
                wt_expr = desugar e;
                wt_type = desugar_type ty;
              };
          )
            :: values
          )
      | `Type (l, params, body) ->
          ( ( desugar_type_binding (SC.var_of_label l, params, body)
              :: types
            )
          , values
          )
    )
  in
  let body = List.fold_right fields ~init:D.EmptyRecord ~f:(fun bind old ->
      match bind.Loc.l_value with
      | `Value (l, _, _) ->
          let l = l.Loc.l_value in
          D.App {
            app_fn = D.App {
                app_fn = D.UpdateVal {
                    uv_lbl = l;
                  };
                app_arg = old;
              };
            app_arg = D.Var {v_var = Ast.var_of_label l};
          }
      | `Type (l, _, _) ->
          let l = l.Loc.l_value in
          D.UpdateType{
            ut_lbl = l;
            ut_type = DT.Var {
                v_info = `Unknown;
                v_var = Ast.var_of_label l;
              };
            ut_record = old;
          }
    )
  in
  D.LetRec {
    letrec_vals = values;
    letrec_types = types;
    letrec_body = body;
  }
and desugar_match cases =
  begin match cases with
    | (Loc.{l_value = SP.Ctor _; _}, _) :: _ ->
        desugar_lbl_match LabelMap.empty cases
    | (Loc.{l_value = SP.Const _; _}, _) :: _ ->
        desugar_const_match ConstMap.empty cases
    | [(pat, body)] ->
        desugar_lambda [pat] body
    | [] -> D.Match
          { cases = LabelMap.empty
          ; default = None
          }
    | (Loc.{l_value = SP.Wild; _}, _) :: cs | (Loc.{l_value = SP.Var _; _}, _) :: cs ->
        unreachable_cases cs
  end
and desugar_const_match dict = function
  | [Loc.{l_value = SP.Wild; _}, body] -> D.ConstMatch
        { cm_default = D.Lam {
              l_param = Gensym.anon_var ();
              l_body = desugar body;
            }
        ; cm_cases = dict
        }
  | (Loc.{l_value = SP.Wild; _}, _) :: cs ->
      unreachable_cases cs
  | [Loc.{l_value = (SP.Var _); _} as p, body] ->
      D.ConstMatch
        { cm_default = desugar_lambda [p] body
        ; cm_cases = dict
        }
  | (Loc.{l_value = SP.Var _; _}, _) :: cs ->
      unreachable_cases cs
  | (Loc.{l_value = SP.Const {const_val = c; _}; _}, body) as case :: rest ->
      begin match Map.find dict c with
        | Some _ ->
            unreachable_cases [case]
        | None ->
            desugar_const_match
              (Map.set dict ~key:c ~data:(desugar body))
              rest
      end
  | [] ->
      incomplete_pattern ()
  | (Loc.{l_value = SP.Ctor _; _}, _) :: _ ->
      MuleErr.throw `MatchDesugarMismatch
and desugar_lbl_match dict = function
  | [] -> D.Match
        { default = None
        ; cases = finalize_dict dict
        }
  | [(Loc.{l_value = SP.Wild; _}, body)] -> D.Match
        { default = Some (None, desugar body)
        ; cases = finalize_dict dict
        }
  | [Loc.{l_value = SP.Var {v_var = v; v_type = None; _}; _}, body] ->
      D.Match
        { default = Some (Some v.Loc.l_value, desugar body)
        ; cases = finalize_dict dict
        }
  | [Loc.{l_value = SP.Var {v_var = v; v_type = Some ty; _}; _}, body] ->
      let v' = Gensym.anon_var () in
      let let_ = D.Let
          { let_v = v.Loc.l_value
          ; let_e =
              D.WithType{
                wt_expr = D.Var {v_var = v'};
                wt_type = desugar_type ty
              }
          ; let_body = desugar body
          }
      in
      D.Match
        { default = Some(Some v', let_)
        ; cases = finalize_dict dict
        }
  | (Loc.{l_value = SP.Ctor {c_lbl = lbl; c_arg = p; _}; _}, body) :: cases ->
      let dict' =
        Map.update dict lbl.Loc.l_value ~f:(function
          | None -> [(p, body)]
          | Some cases -> ((p, body) :: cases)
        )
      in
      desugar_lbl_match dict' cases
  | (_ :: cs) ->
      unreachable_cases cs
and finalize_dict dict =
  Map.map dict
    ~f:( fun cases ->
      let v = Gensym.anon_var () in
      ( v
      , D.App
          { app_fn = desugar_match (List.rev cases)
          ; app_arg = D.Var {v_var = v}
          }
      )
    )
and desugar_let bs body =
  (* As part of the desugaring process, we have to remove all "complex" patterns;
   * in the desugared AST, let bindings only have simple variables as patterns. *)
  let rec go vals types = function
    | [] ->
        D.LetRec {
          letrec_types = types;
          letrec_vals = vals;
          letrec_body = desugar body;
        }
    | `BindType t :: bs ->
        let (v, ty) = desugar_type_binding t in
        go vals ((v, ty) :: types) bs
    | `BindVal (p, e) :: bs ->
        go_val_binding vals types (p.Loc.l_value, desugar e) bs

  and go_val_binding vals types (pat, e) bs = match (pat, e) with
    | (SP.Var {v_var = v; v_type = None; _}, e) ->
        go ((v.Loc.l_value, e) :: vals) types bs
    | ((SP.Const _), _) ->
        incomplete_pattern ()
    | (SP.Wild, e) ->
        go ((Gensym.anon_var (), e) :: vals) types bs
    | (SP.Var{v_var = v; v_type = Some ty; _}, e) ->
        go
          (( v.Loc.l_value
           , D.WithType{
               wt_expr = e;
               wt_type = desugar_type ty
             }
          ) :: vals)
          types
          bs
    | (SP.Ctor{c_lbl = lbl; c_arg = pat; _}, e) ->
        let bind_var = Gensym.anon_var () in
        let match_var = Gensym.anon_var () in
        let bind =
          ( bind_var
          , D.App {
              app_fn =
                D.Match {
                  default = None;
                  cases = LabelMap.singleton lbl.Loc.l_value
                      ( match_var
                      , D.Var {v_var = match_var}
                      )
                };
              app_arg = e;
            }
          )
        in
        go_val_binding
          (bind :: vals)
          types
          (pat.Loc.l_value, D.Var {v_var = bind_var})
          bs
  in
  go [] [] (List.map bs ~f:(fun b -> b.Loc.l_value))
and desugar_type_binding: (SC.var * SC.var list * ST.lt) -> (Ast.Var.t * DK.maybe_kind DT.t) =
  fun (v, params, ty) ->
  let v = v.Loc.l_value in
  let params = List.map params ~f:(fun v -> v.Loc.l_value) in
  (* Here, we convert things like `type t a b = ... (t a b) ...` to
   * `lam a b. rec t. ... t ...`.
  *)
  let ty = DT.Recur {
      mu_info = `Unknown;
      mu_var = v;
      mu_body = substitue_type_apps
          v
          params
          (desugar_type ty);
    }
  in
  let ty =
    List.fold_right
      params
      ~init:ty
      ~f:(fun param tybody ->
        DT.TypeLam {
          tl_info = `Arrow(`Unknown, `Unknown);
          tl_param = param;
          tl_body = tybody;
        }
      )
  in
  (v, ty)
