module SP = Ast.Surface.Pattern
module S = Ast.Surface.Expr
module ST = Ast.Surface.Type
module D = Ast.Desugared.Expr
module C = Ast.Const
module DT = Ast.Desugared.Type
module DK = Ast.Desugared.Kind

let error e =
  raise (MuleErr.MuleExn e)

let incomplete_pattern p =
  error (MuleErr.IncompletePattern p)

let unreachable_case (_p:SP.t) =
  error MuleErr.UnreachableCases

let var_to_lbl v = Ast.Var.to_string v |> Ast.Label.of_string

let rec prune e = match e with
  | D.LetType{letty_binds = []; letty_body} -> prune letty_body
  | _ -> D.apply_to_kids e ~f:prune

let substitue_type_apps: ST.t -> ST.t -> VarSet.t -> ST.t -> ST.t =
  fun old new_ vars ->
  let rec go ty =
    if Poly.equal ty old then
      new_
    else
      begin match ty with
        | ST.Quant{q_quant = q; q_vars = vs; q_body; q_loc} ->
            let shadowed =
              List.fold
                vs
                ~init:false
                ~f:(fun ret var -> ret || Set.mem vars var)
            in
            if shadowed then
              ty
            else
              ST.Quant{
                q_quant = q;
                q_vars = vs;
                q_body = go q_body;
                q_loc;
              }
        | ST.Recur{recur_var = v; recur_body = body} ->
            if Set.mem vars v then
              ty
            else
              ST.Recur{recur_var = v; recur_body = go body}
        | ST.Fn{fn_param = p; fn_ret = r} -> ST.Fn{
            fn_param = go p;
            fn_ret = go r;
          }
        | ST.App{app_fn = f; app_arg = x} -> ST.App{app_fn = go f; app_arg = go x}
        | ST.Union{u_l = l; u_r = r} -> ST.Union{u_l = go l; u_r = go r}
        | ST.Annotated{anno_var; anno_ty; anno_loc} ->
            ST.Annotated {
              anno_var;
              anno_loc;
              anno_ty = go anno_ty;
            }
        | ST.Record {r_items = items} ->
            ST.Record {
              r_items = List.map items ~f:go_record_item;
            }
        | ST.RowRest _ | ST.Var _ | ST.Ctor _ | ST.Path _ | ST.Import _ -> ty
      end
  and go_record_item = function
    | ST.Field(l, t) -> ST.Field(l, go t)
    | ST.Type(_, _, None) as ty -> ty
    | ST.Type(lbl, vs, Some ty) ->
        let shadowed =
          List.fold
            (Ast.var_of_label lbl :: vs)
            ~init:false
            ~f:(fun ret var -> ret || Set.mem vars var)
        in
        if shadowed then
          ST.Type(lbl, vs, Some ty)
        else
          ST.Type(lbl, vs, Some (go ty))
    | ST.Rest v -> ST.Rest v
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
  | ST.Quant{q_quant = q; q_vars = vs; q_body = body; q_loc = _} ->
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
      MuleErr.(throw (IllegalAnnotatedType ty))
  | ST.Path{p_var; p_lbls; _} ->
      DT.Path {p_info = `Unknown; p_var; p_lbls}
  | ST.App{app_fn = f; app_arg = x} ->
      DT.App {
        app_info = `Unknown;
        app_fn = desugar_type' f;
        app_arg = desugar_type' x;
      }
  | ST.Ctor _ ->
      failwith "BUG: ctors should be applied."
and desugar_union_type tail (l, r) =
  match desugar_type' l, desugar_type' r, tail with
  | DT.Union{u_row = (_, lbls_l, None)}, DT.Union{u_row = (_, lbls_r, None)}, (Some v)
  | DT.Union{u_row = (_, lbls_l, None)}, DT.Union{u_row = (_, lbls_r, Some v)}, None
  | DT.Union{u_row = (_, lbls_l, Some v)}, DT.Union{u_row = (_, lbls_r, None)}, None ->
      (`Type, lbls_l @ lbls_r, Some v)
  | DT.Union{u_row = (_, lbls_l, None)}, DT.Union{u_row = (_, lbls_r, None)}, None ->
      (`Type, lbls_l @ lbls_r, None)
  | _ -> raise
        (MuleErr.MuleExn
           (MuleErr.MalformedType
              "Unions must be composed of ctors and at most one ...r"))
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
    | (ST.Rest _ :: _) -> raise
          (MuleErr.MuleExn
             (MuleErr.MalformedType "row variable before the end of a record type."))
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
  | S.Lam {
      lam_params = SP.Var {v_var = v; v_type = None} :: pats;
      lam_body = body;
    } ->
      D.Lam {l_param = v; l_body = desugar (S.Lam {
          lam_params = pats;
          lam_body = body;
        })}
  | S.Lam {
      lam_params = SP.Wild :: pats;
      lam_body =  body;
    } ->
      D.Lam {
        l_param = Gensym.anon_var ();
        l_body = desugar (S.Lam {
            lam_params = pats;
            lam_body = body;
          });
      }
  | S.Lam {
      lam_params = SP.Var {v_var = v; v_type = Some ty} :: pats;
      lam_body = body;
    } ->
      let v' = Gensym.anon_var () in
      D.Lam {
        l_param = v';
        l_body = D.Let {
            let_v = v;
            let_e = D.App {
                app_fn = D.WithType {wt_type = desugar_type ty};
                app_arg = D.Var { v_var = v'};
              };
            let_body = desugar (S.Lam {
                lam_params = pats;
                lam_body = body;
              });
          }
      }
  | S.Lam {lam_params = (SP.Const _) as p :: _; _} ->
      incomplete_pattern p
  | S.Lam {
      lam_params = pat :: pats;
      lam_body = body;
    } ->
      let var = Gensym.anon_var () in
      D.Lam {
        l_param = var;
        l_body = desugar
            (S.Match {
                match_arg = S.Var {v_var = var};
                match_cases =
                  [ ( pat
                    , S.Lam {
                        lam_params = pats;
                        lam_body = body;
                      }
                    )
                  ]
              }
            );
      }
  | S.Lam {
      lam_params = [];
      lam_body = body;
    } -> desugar body
  | S.Record {r_fields = []} -> D.EmptyRecord
  | S.Record {r_fields = fields} -> desugar_record fields
  | S.Update{up_arg = e; up_fields = []} ->
      desugar e
  | S.Update{up_arg = e; up_fields = `Value (l, _, v) :: fs} ->
      D.App {
        app_fn = D.App {
            app_fn = D.Update {
                up_level = `Value;
                up_lbl = l;
              };
            app_arg = desugar (S.Update {
                up_arg = e;
                up_fields = fs;
              });
          };
        app_arg = desugar v;
      }
  | S.Update {
      up_arg = e;
      up_fields = `Type (lbl, params, ty) :: fs;
    } ->
      let (_, ty) = desugar_type_binding (Ast.var_of_label lbl, params, ty) in
      D.App {
        app_fn = D.App {
            app_fn = D.Update {
                up_level = `Type;
                up_lbl = lbl;
              };
            app_arg = desugar (S.Update {
                up_arg = e;
                up_fields = fs;
              });
          };
        app_arg = D.Witness {wi_type = ty};
      }
  | S.GetField {gf_arg = e; gf_lbl = l} ->
      D.App {
        app_fn = D.GetField {
            gf_strategy = `Strict;
            gf_lbl = l;
          };
        app_arg =  desugar e;
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
and desugar_record fields =
  let record_var = Gensym.anon_var () in
  let get_record_field lbl =
    D.App {
      app_fn = D.GetField {
          gf_strategy = `Lazy;
          gf_lbl = lbl;
        };
      app_arg = D.Var {v_var = record_var};
    }
  in
  let label_map =
    List.filter_map fields ~f:(function
        | `Value (l, ty, _) ->
            Some (l, ty)
        | `Type _ -> None)
    |> Map.of_alist_exn (module Ast.Label)
  in
  let rec subst env expr = match expr with
    (* TODO: do stuff with type variables *)
    | D.Const c -> D.Const c
    | D.Var {v_var = v} ->
        let lbl = var_to_lbl v in
        begin match Map.find env lbl with
          | None -> D.Var {v_var = v}
          | Some None -> get_record_field lbl
          | Some (Some ty) ->
              D.App {
                app_fn = D.WithType {wt_type = desugar_type ty};
                app_arg = get_record_field lbl;
              }
        end
    | D.Ctor{ c_lbl; c_arg } ->
        D.Ctor{ c_lbl; c_arg = subst env c_arg }
    | D.Lam {l_param; l_body} ->
        D.Lam {
          l_param;
          l_body = subst
              (Map.remove env (var_to_lbl l_param))
              l_body;
        }
    | D.App{ app_fn = f; app_arg = x } ->
        D.App {
          app_fn = subst env f;
          app_arg = subst env x;
        }
    | D.Match {cases; default} ->
        D.Match
          { cases =
              Map.map cases ~f:(fun (var, body) ->
                  let env' = Map.remove env (var_to_lbl var) in
                  ( var
                  , subst env' body
                  )
                )
          ; default = Option.map default ~f:(function
                | (None, body) -> (None, subst env body)
                | (Some var, body) ->
                    ( Some var
                    , let env' = Map.remove env (var_to_lbl var) in
                      subst env' body
                    )
              )
          }
    | D.ConstMatch {cm_cases; cm_default} ->
        D.ConstMatch
          { cm_cases = Map.map cm_cases ~f:(subst env)
          ; cm_default = subst env cm_default
          }
    | D.Let{let_v; let_e; let_body} ->
        D.Let
          { let_v
          ; let_e = subst env let_e
          ; let_body = subst (Map.remove env (var_to_lbl let_v)) let_body
          }
    | D.LetType{letty_binds; letty_body} ->
        D.LetType{letty_binds; letty_body = subst env letty_body}
    | D.Fix _ | D.EmptyRecord | D.GetField _ | D.Update _ | D.WithType _ | D.Witness _ ->
        expr
  in
  let build_record fields =
    let types = List.filter_map fields ~f:(function
        | `Type (lbl, params, body) ->
            Some
              ( desugar_type_binding
                  ( Ast.var_of_label lbl
                  , params
                  , body
                  )
              )
        | `Value _ ->
            None
      )
    in
    D.LetType
      { letty_binds = types
      ; letty_body = List.fold_right
            fields
            ~init:D.EmptyRecord
            ~f:(fun field old ->
                match field with
                | `Type (lbl, _, _) ->
                    D.App {
                      app_fn = D.App {
                          app_fn = D.Update {
                              up_level = `Type;
                              up_lbl = lbl;
                            };
                          app_arg = old;
                        };
                      app_arg = D.Witness {
                          wi_type = DT.Var {
                              v_info = `Unknown;
                              v_var = Ast.var_of_label lbl;
                            };
                        };
                    }
                | `Value(l, ty, v) ->
                    let v' =
                      begin match ty with
                        | None -> v
                        | Some ty' -> S.WithType {
                            wt_term = v;
                            wt_type = ty';
                          }
                      end
                    in
                    D.App {
                      app_fn = D.App {
                          app_fn = D.Update {
                              up_level = `Value;
                              up_lbl = l;
                            };
                          app_arg = old;
                        };
                      app_arg = subst label_map (desugar v');
                    }
              )
      }
  in
  D.App {
    app_fn = D.Fix { fix_type = `Record };
    app_arg = D.Lam {
        l_param = record_var;
        l_body = build_record fields;
      }
  }
and desugar_match cases =
  begin match cases with
    | ((SP.Ctor _, _) :: _) ->
        desugar_lbl_match LabelMap.empty cases
    | ((SP.Const _, _) :: _) ->
        desugar_const_match ConstMap.empty cases
    | [(pat, body)] ->
        desugar (S.Lam {
            lam_params = [pat];
            lam_body =  body;
          })
    | [] -> D.Match
          { cases = LabelMap.empty
          ; default = None
          }
    | ((SP.Wild, _) :: _) | ((SP.Var _, _) :: _) ->
        unreachable_case SP.Wild
  end
and desugar_const_match dict = function
  | [(SP.Wild, body)] -> D.ConstMatch
        { cm_default = D.Lam {
              l_param = Gensym.anon_var ();
              l_body = desugar body;
            }
        ; cm_cases = dict
        }
  | ((SP.Wild, _) :: _) ->
      unreachable_case SP.Wild
  | [(SP.Var _) as p, body] ->
      D.ConstMatch
        { cm_default = desugar (S.Lam{
              lam_params = [p];
              lam_body =  body;
            })
        ; cm_cases = dict
        }
  | ((SP.Var _, _) :: _) ->
      unreachable_case SP.Wild
  | ((SP.Const {const_val = c}, body) :: rest) ->
      begin match Map.find dict c with
        | Some _ -> unreachable_case (SP.Const {const_val = c})
        | None ->
            desugar_const_match
              (Map.set dict ~key:c ~data:(desugar body))
              rest
      end
  | [] ->
      (* TODO: what should the argument actually be here? *)
      incomplete_pattern SP.Wild
  | ((SP.Ctor _, _) :: _) ->
      error
        (MuleErr.TypeError
           (* FIXME: "constant" isn't the name of a type; this will be
            * confusing. *)
           (MuleErr.MismatchedCtors (`Named "union", `Named "constant")))
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
  | (_ :: _) ->
      raise MuleErr.(MuleExn UnreachableCases)
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
and desugar_let bs body = match simplify_bindings bs with
  | [] ->
      (* Shouldn't ever happen, but the correct behavior is clear. *)
      desugar body
  | [`Value(v, e)] ->
      D.Let
        { let_v = v
        ; let_e = D.App {
              app_fn = D.Fix { fix_type = `Let };
              app_arg = D.Lam {
                  l_param = v;
                  l_body = desugar e;
                }
            }
        ; let_body = desugar body
        }
  | [`Type t] ->
      let (v, ty) = desugar_type_binding t in
      D.LetType {
        letty_binds = [v, ty];
        letty_body = desugar body;
      }
  | bindings ->
      let record =
        List.map bindings ~f:(function
            | `Value(v, S.WithType{wt_term = e; wt_type = ty}) ->
                `Value(Ast.var_to_label v, Some ty, e)
            | `Value (v, e) ->
                `Value(Ast.var_to_label v, None, e)
            | `Type (f, params, body) ->
                `Type(Ast.var_to_label f, params, body)
          )
        |> desugar_record
      in
      let record_name = Gensym.anon_var () in
      let body =
        List.fold bindings ~init:(desugar body) ~f:(fun accum bind ->
            match bind with
            | `Value(v, _) ->
                D.Let {
                  let_v = v;
                  let_e = D.App {
                      app_fn = D.GetField {
                          gf_strategy = `Strict;
                          gf_lbl = Ast.var_to_label v;
                        };
                      app_arg = D.Var {v_var = record_name};
                    };
                  let_body = accum;
                }
            | `Type t ->
                let (v, ty) = desugar_type_binding t in
                D.LetType
                  { letty_binds =
                      [ v
                      , DT.Path {
                          p_info = DT.get_info ty;
                          p_var = record_name;
                          p_lbls = [var_to_lbl v];
                        }
                      ]
                  ; letty_body = accum
                  }
          )
      in
      D.Let{let_v = record_name; let_e = record; let_body = body}
and desugar_type_binding (v, params, ty) =
  (* Here, we convert things like `type t a b = ... (t a b) ...` to
   * `lam a b. rec t. ... t ...`.
  *)
  let target =
    List.fold_left
      params
      ~init:(ST.Var {v_var = v})
      ~f:(fun f x -> ST.App {
          app_fn = f;
          app_arg = ST.Var {v_var = x};
        })
  in
  let ty =
    ST.Recur
      { recur_var = v
      ; recur_body = substitue_type_apps
            target
            (ST.Var {v_var = v})
            (Set.of_list (module Ast.Var) params)
            ty
      }
  in
  let ty =
    List.fold_right
      params
      ~init:(desugar_type ty)
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
