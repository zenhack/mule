module SP = Ast.Surface.Pattern
module S = Ast.Surface.Expr
module ST = Ast.Surface.Type
module D = Ast.Desugared.Expr
module C = Ast.Const
module DT = Ast.Desugared.Type
module DK = Ast.Desugared.Kind

let incomplete_pattern p =
  MuleErr.throw (`IncompletePattern p)

let unreachable_cases cases =
  MuleErr.throw (`UnreachableCases cases)

let rec prune e = match e with
  | D.LetType{letty_binds = []; letty_body} -> prune letty_body
  | _ -> D.apply_to_kids e ~f:prune

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
  and go_row (info, fields, var) =
    ( info
    , List.map fields ~f:(fun (lbl, t) -> (lbl, go t))
    , var
    )
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
  | DT.Record {r_src; r_info; r_types = (i, fields, rest); r_values} ->
      let vars = ref [] in
      let fields' = List.map fields ~f:(fun (lbl, ty) ->
          match quantify_opaques ty with
          | DT.Opaque {o_info} ->
              let var = Gensym.anon_var () in
              vars := var :: !vars;
              (lbl, DT.Var { v_info = o_info; v_var = var })
          | ty' -> (lbl, ty')
        )
      in
      let init =
        DT.Record
          { r_info
          ; r_src
          ; r_types = (i, fields', rest)
          ; r_values = quantify_row_opaques r_values
          }
      in
      List.fold !vars ~init ~f:(fun ty v ->
          DT.Quant {
            q_info = `Unknown;
            q_quant = `Exist;
            q_var = v;
            q_body = ty;
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
and quantify_row_opaques (i, fields, rest) =
  ( i
  , List.map
      fields
      ~f:(fun (lbl, ty) -> (lbl, quantify_opaques ty))
  , rest
  )

let rec desugar_type' = function
  | ST.Import _ ->
      failwith "TODO: implememnt import type"
  | ST.Fn{fn_param = ST.Annotated{anno_var; anno_ty = param; _}; fn_ret = ret} ->
      DT.Fn {
        fn_info = `Type;
        fn_pvar = Some anno_var;
        fn_param = desugar_type' param;
        fn_ret = desugar_type' ret;
      }
  | ST.Fn{fn_param = param; fn_ret = ret} ->
      DT.Fn {
        fn_info = `Type;
        fn_pvar = None;
        fn_param = desugar_type' param;
        fn_ret = desugar_type' ret;
      }
  | ST.Quant{q_quant = q; q_vars = vs; q_body = body} ->
      List.fold_right
        vs
        ~init:(desugar_type' body)
        ~f:(fun v body -> DT.Quant {
            q_info = `Type;
            q_quant = q;
            q_var = v;
            q_body = body;
          }
          )
  | ST.Recur{recur_var = v; recur_body = body} ->
      DT.Recur {
        mu_info = `Type;
        mu_var = v;
        mu_body = desugar_type' body;
      }
  | ST.Var {v_var = v} ->
      DT.Var{v_info = `Unknown; v_var = v}
  | ST.Union {u_l; u_r} ->
      DT.Union {u_row = desugar_union_type None (u_l, u_r) }
  | ST.Record {r_items = r} ->
      desugar_record_type [] [] r
  | ST.App{app_fn = ST.Ctor{c_lbl; _}; app_arg = t} ->
      DT.Union {
        u_row = (`Type, [(c_lbl, desugar_type' t)], None);
      }
  | ST.RowRest {rr_var = v} ->
      DT.Union { u_row = (`Type, [], Some v) }
  | (ST.Annotated _) as ty ->
      MuleErr.throw (`IllegalAnnotatedType ty)
  | ST.Path{p_var; p_lbls; _} ->
      DT.Path {p_info = `Unknown; p_var; p_lbls}
  | ST.App{app_fn = f; app_arg = x} ->
      DT.App {
        app_info = `Unknown;
        app_fn = desugar_type' f;
        app_arg = desugar_type' x;
      }
  | ST.Ctor _ ->
      MuleErr.bug "ctors should be applied."
and desugar_union_type tail (l, r) =
  match desugar_type' l, desugar_type' r, tail with
  | DT.Union{u_row = (_, lbls_l, None)}, DT.Union{u_row = (_, lbls_r, None)}, (Some v)
  | DT.Union{u_row = (_, lbls_l, None)}, DT.Union{u_row = (_, lbls_r, Some v)}, None
  | DT.Union{u_row = (_, lbls_l, Some v)}, DT.Union{u_row = (_, lbls_r, None)}, None ->
      (`Type, lbls_l @ lbls_r, Some v)
  | DT.Union{u_row = (_, lbls_l, None)}, DT.Union{u_row = (_, lbls_r, None)}, None ->
      (`Type, lbls_l @ lbls_r, None)
  | _ ->
      MuleErr.throw
        (`MalformedType
           "Unions must be composed of ctors and at most one ...r")
and desugar_record_type types fields r =
  let r_src = ST.Record {r_items = r} in
  let rec go types fields = function
    (* TODO: how do we have variable fields for the type row? *)
    | (ST.Type(lbl, params, Some t) :: fs) ->
        let (_, ty) = desugar_type_binding (Ast.var_of_label lbl, params, t) in
        go ((lbl, ty)::types) fields fs
    | (ST.Type(lbl, params, None) :: fs) ->
        let kind =
          List.fold
            params
            ~init:`Unknown
            ~f:(fun k _ -> `Arrow(`Unknown, k))
        in
        go ((lbl, DT.Opaque {o_info = kind})::types) fields fs
    | [] ->
        DT.Record
          { r_src
          ; r_info = `Type
          ; r_types = (`Row, types, None)
          ; r_values = (`Row, fields, None)
          }
    | [ST.Rest v] ->
        DT.Record
          { r_src
          ; r_info = `Type
          ; r_types = (`Row, types, None)
          ; r_values = (`Row, fields, Some v)
          }
    | (ST.Field (l, t) :: rest) ->
        go types ((l, desugar_type' t)::fields) rest
    | (ST.Rest _ :: _) ->
        MuleErr.throw
          (`MalformedType "row variable before the end of a record type.")
  in
  go types fields r
and desugar_type t =
  desugar_type' t
  |> quantify_opaques
and desugar = function
  | S.Import _ -> failwith "TODO: implement import"
  | S.Embed _ -> failwith "TODO: implement embed"
  | S.Const {const_val = c} -> D.Const {const_val = c}
  | S.Var {v_var = v} -> D.Var {v_var = v}
  | S.App{app_fn = f; app_arg = x} -> D.App {
      app_fn = desugar f;
      app_arg = desugar x;
    }
  | S.Lam{lam_params; lam_body} -> desugar_lambda lam_params lam_body
  | S.Record {r_fields = []} -> D.EmptyRecord
  | S.Record {r_fields = fields} -> desugar_record fields
  | S.Update{up_arg; up_fields} -> desugar_update up_arg up_fields
  | S.GetField {gf_arg = e; gf_lbl = l} ->
      D.App {
        app_fn = D.GetField {
            gf_strategy = `Strict;
            gf_lbl = l;
          };
        app_arg = desugar e;
      }
  | S.Ctor {c_lbl = label} ->
      (* The choice of variable name here doesn't matter, since
       * there's nothing we need to worry about shadowing. *)
      let l_param = Ast.Var.of_string "x" in
      D.Lam {
        l_param;
        l_body = D.Ctor {
            c_lbl = label;
            c_arg = D.Var {v_var = l_param };
          };
      }
  | S.Match {match_arg = e; match_cases = cases} ->
      D.App {
        app_fn = desugar_match cases;
        app_arg = desugar e;
      }
  | S.WithType{wt_term = e; wt_type = ty} ->
      D.App {
        app_fn = D.WithType {wt_type = desugar_type ty};
        app_arg = desugar e;
      }
  | S.Let {
      let_binds = bindings;
      let_body = body;
    } ->
      desugar_let bindings body
and desugar_update e fields =
  match fields with
  | [] -> desugar e
  | `Value (l, _, v) :: fs ->
      D.App {
        app_fn = D.App {
            app_fn = D.Update {
                up_level = `Value;
                up_lbl = l;
              };
            app_arg = desugar_update e fs
          };
        app_arg = desugar v;
      }
  | `Type (lbl, params, ty) :: fs ->
      let (_, ty) = desugar_type_binding (Ast.var_of_label lbl, params, ty) in
      D.App {
        app_fn = D.App {
            app_fn = D.Update {
                up_level = `Type;
                up_lbl = lbl;
              };
            app_arg = desugar_update e fs
          };
        app_arg = D.Witness {wi_type = ty};
      }
and desugar_lambda ps body =
  match ps with
  | [] -> desugar body
  | (SP.Var {v_var; v_type = None} :: pats) ->
      D.Lam {l_param = v_var; l_body = desugar_lambda pats body}
  | (SP.Wild :: pats) ->
      D.Lam {
        l_param = Gensym.anon_var ();
        l_body = desugar_lambda pats body;
      }
  | (SP.Var {v_var; v_type = Some ty} :: pats) ->
      D.Lam {
        l_param = v_var;
        l_body = D.Let {
            let_v = v_var;
            let_e = D.App {
                app_fn = D.WithType {wt_type = desugar_type ty};
                app_arg = D.Var {v_var};
              };
            let_body = desugar_lambda pats body;
          }
      }
  | ((SP.Const _) as p :: _) -> incomplete_pattern p
  | (SP.Ctor{c_lbl; c_arg} :: pats) ->
      let v = Gensym.anon_var () in
      D.Match {
        default = None;
        cases = LabelMap.singleton
            c_lbl
            ( v
            , D.App {
                app_fn = desugar_lambda (c_arg :: pats) body;
                app_arg = D.Var {v_var = v}
              }
            )
      }
and desugar_record fields =
  let types, values =
    List.fold_right fields ~init:([], []) ~f:(fun bind (types, values) ->
        match bind with
        | `Value(l, None, e) -> (types, ((Ast.var_of_label l, desugar e) :: values))
        | `Value(l, Some ty, e) ->
            ( types
            , ( Ast.var_of_label l
              , D.App {
                  app_fn = D.WithType {wt_type = desugar_type ty};
                  app_arg = desugar e;
                }
              )
              :: values
            )
        | `Type (l, params, body) ->
            ( ( desugar_type_binding (Ast.var_of_label l, params, body)
              :: types
              )
            , values
            )
      )
  in
  let body = List.fold_right fields ~init:D.EmptyRecord ~f:(fun bind old ->
      match bind with
        | `Value (l, _, _) ->
            D.App {
              app_fn = D.App {
                app_fn = D.Update {
                  up_level = `Value;
                  up_lbl = l;
                };
                app_arg = old;
              };
              app_arg = D.Var {v_var = Ast.var_of_label l};
            }
        | `Type (l, _, _) ->
            D.App {
              app_fn = D.App {
                app_fn = D.Update {
                  up_level = `Type;
                  up_lbl = l;
                };
                app_arg = old;
              };
              app_arg = D.Witness {
                  wi_type = DT.Var {
                      v_info = `Unknown;
                      v_var = Ast.var_of_label l;
                    }
              };
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
    | ((SP.Ctor _, _) :: _) ->
        desugar_lbl_match LabelMap.empty cases
    | ((SP.Const _, _) :: _) ->
        desugar_const_match ConstMap.empty cases
    | [(pat, body)] ->
        desugar_lambda [pat] body
    | [] -> D.Match
          { cases = LabelMap.empty
          ; default = None
          }
    | ((SP.Wild, _) :: cs) | ((SP.Var _, _) :: cs) ->
        unreachable_cases cs
  end
and desugar_const_match dict = function
  | [(SP.Wild, body)] -> D.ConstMatch
        { cm_default = D.Lam {
              l_param = Gensym.anon_var ();
              l_body = desugar body;
            }
        ; cm_cases = dict
        }
  | ((SP.Wild, _) :: cs) ->
      unreachable_cases cs
  | [(SP.Var _) as p, body] ->
      D.ConstMatch
        { cm_default = desugar_lambda [p] body
        ; cm_cases = dict
        }
  | ((SP.Var _, _) :: cs) ->
      unreachable_cases cs
  | ((SP.Const {const_val = c}, body) as case :: rest) ->
      begin match Map.find dict c with
        | Some _ ->
            unreachable_cases [case]
        | None ->
            desugar_const_match
              (Map.set dict ~key:c ~data:(desugar body))
              rest
      end
  | [] ->
      (* TODO: what should the argument actually be here? *)
      incomplete_pattern SP.Wild
  | ((SP.Ctor _, _) :: _) ->
      MuleErr.throw `MatchDesugarMismatch
and desugar_lbl_match dict = function
  | [] -> D.Match
        { default = None
        ; cases = finalize_dict dict
        }
  | [(SP.Wild, body)] -> D.Match
        { default = Some (None, desugar body)
        ; cases = finalize_dict dict
        }
  | [SP.Var {v_var = v; v_type = None}, body] ->
      D.Match
        { default = Some (Some v, desugar body)
        ; cases = finalize_dict dict
        }
  | [SP.Var {v_var = v; v_type = Some ty}, body] ->
      let v' = Gensym.anon_var () in
      let let_ = D.Let
          { let_v = v
          ; let_e = D.App {
                app_fn = D.WithType{wt_type = desugar_type ty};
                app_arg = D.Var {v_var = v'};
              }
          ; let_body = desugar body
          }
      in
      D.Match
        { default = Some(Some v', let_)
        ; cases = finalize_dict dict
        }
  | (SP.Ctor {c_lbl = lbl; c_arg = p}, body) :: cases ->
      let dict' =
        Map.update dict lbl ~f:(function
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
            { app_fn = desugar_lbl_match LabelMap.empty (List.rev cases)
            ; app_arg = D.Var {v_var = v}
            }
        )
      )
and desugar_let bs body =
  let rec go vals types = function
    | `Value(v, e) :: fs ->
        go ((v, desugar e) :: vals) types fs
    | `Type t :: fs ->
        let (v, ty) = desugar_type_binding t in
        go vals ((v, ty) :: types) fs
    | [] ->
        D.LetRec {
          letrec_types = types;
          letrec_vals = vals;
          letrec_body = desugar body;
        }
  in
  go [] [] (simplify_bindings bs)
and desugar_type_binding (v, params, ty) =
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
and simplify_bindings = function
  (* Simplify a list of bindings, such that there are no "complex" patterns;
   * everything is a simple variable. *)
  | [] -> []
  | `BindType t :: bs ->
      `Type t :: simplify_bindings bs
  | `BindVal (SP.Var {v_var = v; v_type = None}, e) :: bs ->
      `Value(v, e) :: simplify_bindings bs
  | `BindVal((SP.Const _) as p, _) :: _ ->
      incomplete_pattern p
  | `BindVal(SP.Wild, e) :: bs  ->
      `Value(Gensym.anon_var (), e) :: simplify_bindings bs
  | `BindVal(SP.Var{v_var = v; v_type = Some ty}, e) :: bs ->
      `Value(v, S.WithType{wt_term = e; wt_type = ty}) :: simplify_bindings bs
  | `BindVal(SP.Ctor{c_lbl = lbl; c_arg = pat}, e) :: bs ->
      let bind_var = Gensym.anon_var () in
      let match_var = Gensym.anon_var () in
      `Value
        ( bind_var
        , S.Match
            { match_arg = e
            ; match_cases =
                [ ( SP.Ctor{c_lbl = lbl; c_arg = SP.Var {v_var = match_var; v_type = None}}
                  , S.Var {v_var = match_var}
                  )
                ]
            }
        )
      :: simplify_bindings (`BindVal(pat, S.Var {v_var = bind_var}) :: bs)


let desugar e =
  prune (desugar e)
