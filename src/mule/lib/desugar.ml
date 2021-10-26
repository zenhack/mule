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
module DC = Desugared_ast_common

let incomplete_pattern () =
  MuleErr.throw `IncompletePattern

let unreachable_cases cases =
  MuleErr.throw (`UnreachableCases cases)

let sort_binds: fv:('a -> VarSet.t) -> (Var.t * 'a) list -> (Var.t * 'a) Tsort.result =
  fun ~fv nodes ->
  let vars =
    List.fold nodes ~init:(Set.empty (module Var)) ~f:(fun set (v, _) -> Set.add set v)
  in
  let edges =
    List.map nodes ~f:(fun (from, def) ->
      Set.inter vars (fv def)
      |> Set.to_list
      |> List.map ~f:(fun to_ -> Tsort.{from; to_})
    )
    |> List.concat
  in
  let sorted_vars =
    Tsort.sort
      (module Var)
      ~nodes:(Set.to_list vars)
      ~edges
  in
  let map = Map.of_alist_exn (module Var) nodes in
  Tsort.Result.map
    sorted_vars
    ~f:(fun v -> (v, Util.find_exn map v))

let build_sorted
  : bindings:('a Tsort.result)
    -> body:('i D.t)
    -> recursive:('a NonEmpty.t -> 'i D.t -> 'i D.t)
    -> nonrecursive:('a -> 'i D.t -> 'i D.t)
    -> 'i D.t =
  fun ~bindings ~body ~recursive ~nonrecursive ->
  List.fold_right bindings ~init:body ~f:(fun binding body ->
    match binding with
    | `Single x ->
        nonrecursive x body
    | `Cycle binds ->
        recursive binds body
  )
let build_sorted_let_vals: (Var.t * 'a D.t) Tsort.result -> 'a D.t -> 'a D.t =
  fun bindings body ->
  build_sorted ~bindings ~body
    ~recursive:(fun binds body ->
      D.(LetRec {
          letrec_binds = {
            rec_types = [];
            rec_vals =
              NonEmpty.map binds ~f:(fun (v, e) -> (v, None, e))
              |> NonEmpty.to_list;
          };
          letrec_body = body;
        })
    )
    ~nonrecursive:(fun (v, e) body ->
      D.Let {
        let_v = v;
        let_e = e;
        let_body = body;
      }
    )

let _ = build_sorted_let_vals (* temporary, silence unused val warning from ocamlc. *)

let sort_let_types: (Var.t * 'i DT.t) list -> (Var.t * 'i DT.t) list list =
  fun nodes ->
  List.map (sort_binds ~fv:DT.ftv nodes) ~f:(function
    (* TODO: manage cycles vs. singles differently. *)
    | `Cycle (v, vs) -> v::vs
    | `Single v -> [v]
  )

let sort_let ~rec_types ~rec_vals ~letrec_body =
  let vals = List.map rec_vals ~f:(fun (v, t, e) -> match t with
      | None -> (v, e)
      | Some (t, src) ->
          ( v
          , D.(App {
              app_fn = WithType { wt_src = src; wt_type = t };
              app_arg = e;
            })
          )
    )
  in
  let vals = sort_binds ~fv:D.fv vals in
  D.(LetRec {
      letrec_binds = {
        rec_types = sort_let_types rec_types;
        rec_vals = [];
      };
      letrec_body =
        build_sorted_let_vals vals letrec_body;
  })

(* [substitute_type_apps f params ty] replaces occurances of [f] applied to
 * the list of parameters in [ty] with just [f]. *)
let substitue_type_apps
  : Ast.Var.t
    -> Ast.Var.t Ast.Loc.located
    -> Ast.Var.t list
    -> DK.maybe_kind DT.t
    -> DK.maybe_kind DT.t =
  fun fvar vloc params ->
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
    | DT.Row _
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
      DT.Var {
        v_var = fvar;
        v_src = `Sourced vloc;
        v_info = `Unknown;
      }
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
        | DT.Quant{q_info; q_quant; q_var; q_bound; q_body} ->
            DT.Quant{
              q_info;
              q_quant;
              q_var;
              q_bound = Option.map q_bound ~f:go;
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
        | DT.Row{r_row} ->
            DT.Row{r_row = go_row r_row}
      end
  and go_row {row_info; row_fields; row_rest} = {
    row_info;
    row_fields = List.map row_fields ~f:(fun (lbl, t) -> (lbl, go t));
    row_rest;
  }
  in
  go

let rec hoist_assoc_types t = match DT.apply_to_kids t ~f:hoist_assoc_types with
  | (DT.Record {r_types; _}) as init ->
      List.fold r_types.row_fields ~init ~f:(fun old (lbl, ty) ->
        DT.subst
          (var_of_label lbl)
          ty
          old
      )
  | t -> t


let rec quantify_opaques t = match DT.apply_to_kids t ~f:quantify_opaques with
  (* Transform opaque type members into existentials, e.g.
   *
   * { type t }
   *
   * becomes:
   *
   * exist a. { type t = a }
  *)
  | DT.Record {r_src; r_info; r_types = {row_info; row_fields; row_rest}; r_values} ->
      let vars = ref [] in
      let row_fields = List.map row_fields ~f:(fun (lbl, ty) ->
          match ty with
          | DT.Opaque {o_info} ->
              let var = Gensym.anon_var Gensym.global in
              vars := var :: !vars;
              (lbl, DT.Var {
                   v_info = o_info;
                   v_var = var;
                   v_src = `Generated;
                 })
          | ty' -> (lbl, ty')
        )
      in
      let init =
        DT.Record {
          r_info;
          r_src;
          r_values;
          r_types = {row_info; row_fields; row_rest};
        }
      in
      List.fold !vars ~init ~f:(fun ty v ->
        DT.Quant {
          q_info = `Unknown;
          q_quant = `Exist;
          q_var = v;
          q_bound = None;
          q_body = ty;
        }
      )
  | t -> t

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
        ~f:(fun (v, bound) body -> DT.Quant {
            q_info = `Type;
            q_quant = q.Loc.l_value;
            q_var = v.Loc.l_value;
            q_bound = Option.map ~f:desugar_type' bound;
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
      DT.Var{
        v_info = `Unknown;
        v_var = v.Loc.l_value;
        v_src = `Sourced v;
      }
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
  | ST.RowRest rest ->
      DT.Union {
        u_row = {
          row_info = `Type;
          row_fields = [];
          row_rest = Some (desugar_type' rest);
        };
      }
  | ST.Annotated _ ->
      MuleErr.throw (`IllegalAnnotatedType ty)
  | ST.Path{p_var; p_lbls; _} ->
      let (p_var, src) = match p_var with
        | `Var Loc.{l_value; l_loc} ->
            ( `Var l_value
            , Loc.{l_value = `Var l_value; l_loc}
            )
        | `Import Loc.{l_value; l_loc} ->
            ( `Import (desugar_import l_loc l_value)
            , Loc.{l_value = `Import l_value; l_loc}
            )
      in
      DT.Path {
        p_info = `Unknown;
        p_var;
        p_lbls = List.map p_lbls ~f:(fun Loc.{l_value = l; _} -> l);
        p_src = `Sourced src;
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
        DT.Record {
          r_src;
          r_info = `Type;
          r_types = {row_info = `Row; row_fields = types; row_rest = None};
          r_values = {row_info = `Row; row_fields = fields; row_rest = None};
        }
    | [ST.Rest t] ->
        DT.Record {
          r_src;
          r_info = `Type;
          r_types = {row_info = `Row; row_fields = types; row_rest = None};
          r_values = {
            row_info = `Row;
            row_fields = fields;
            row_rest = Some (desugar_type' t)
          };
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
  |> hoist_assoc_types
and desugar_import imp_loc ({i_path; i_from} as i) =
  let Loc.{l_value; l_loc} = i_path in
  {
    i_loc = Some l_loc;
    i_orig_path = l_value;
    i_resolved_path =
      Paths.resolve_path
        ~here:i_from
        ~loc:l_loc
        ~target:l_value;
    i_src = `SurfaceImport Loc.{
        l_loc = imp_loc;
        l_value = i;
      };
  }
and desugar (Loc.{l_value = e; l_loc} as le) = match e with
  | S.Import i ->
      D.Import (desugar_import l_loc i)
  | S.Embed {e_path; e_from; _} ->
      D.Embed {
        e_path;
        e_src = le;
        e_value = Paths.resolve_embed
            ~loc:l_loc
            ~here:e_from
            ~target:e_path;
      }
  | S.Const {const_val = c; _} -> D.Const {const_val = c}
  | S.Var {v_var = v; _} ->
      D.Var {
        v_var = v.Loc.l_value;
        v_src = `Sourced v;
      }
  | S.App{app_fn = f; app_arg = x; _} -> D.App {
      app_fn = desugar f;
      app_arg = desugar x;
    }
  | S.Lam{lam_params; lam_body; _} -> desugar_lambda le lam_params lam_body
  | S.List {l_elts} ->
      let empty =
        D.GetField {
          gf_lbl = Label.of_string "empty";
          gf_record = D.Import (DC.import_abs `Generated "list");
        }
      in
      let cons =
        D.GetField {
          gf_lbl = Label.of_string "push";
          gf_record = D.GetField {
              gf_lbl = Label.of_string "left";
              gf_record = D.Import (DC.import_abs `Generated "list");
            };
        }
      in
      List.fold_right
        l_elts
        ~init:empty
        ~f:(fun hd tl ->
          D.App {
            app_fn = D.App {
                app_fn = cons;
                app_arg = desugar hd;
              };
            app_arg = tl;
          }
        )
  | S.Record {r_fields = fields; _} -> desugar_record fields
  | S.Update{up_arg; up_fields; _} -> desugar_update up_arg up_fields
  | S.GetField {gf_arg = e; gf_lbl = l; _} ->
      D.GetField {
        gf_lbl = l.Loc.l_value;
        gf_record = desugar e;
      }
  | S.Ctor {c_lbl = label; _} ->
      (* The choice of variable name here doesn't matter, since
       * there's nothing we need to worry about shadowing. *)
      let l_param = Ast.Var.of_string "x" in
      D.Lam {
        l_param;
        l_src = `Ctor label;
        l_body = D.Ctor {
            c_lbl = label.Loc.l_value;
            c_arg = D.Var {
                v_var = l_param;
                v_src = `Generated
              };
          };
      }
  | S.Match {match_arg = e; match_cases = cases; _} ->
      D.App {
        app_fn = D.Match {
            m_branch = desugar_match cases;
            m_src = `Generated;
          };
        app_arg = desugar e;
      }
  | S.WithType{wt_term = e; wt_type = ty; _} ->
      D.App {
        app_fn =  D.WithType {
            wt_src = `WithType(e, ty);
            wt_type = desugar_type ty;
          };
        app_arg = desugar e;
      }
  | S.Let {
      let_binds = bindings;
      let_body = body;
      _;
    } ->
      desugar_let bindings body
  | S.Quote _ | S.Unquote _ | S.UnquoteSplice _ ->
      MuleErr.throw (`NotImplemented (String.concat [
          "Quote and unquote operators are not yet implemented. ";
          "Progress on the macro system is tracked at:\n\n\t";
          "https://gitlab.com/isd/mule/issues/7";
        ]))
and desugar_update e fields =
  let rec go e = function
    | [] -> desugar e
    | `Value (l, _, v) :: fs ->
        D.UpdateVal {
          uv_lbl = l.Loc.l_value;
          uv_val = desugar v;
          uv_record = go e fs;
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
and desugar_lambda src ps body =
  let ctr = Gensym.global in
  let rec go arg_idx pat_depth =
    let l_src p = `PartialLambda(arg_idx, p, pat_depth, src) in function
      | [] -> desugar body

      | (Loc.{l_value = SP.Var {v_var; v_type = None; _}; _} as p :: pats) ->
          D.Lam {
            l_src = l_src p;
            l_param = v_var.Loc.l_value;
            l_body = go (arg_idx + 1) 0 pats;
          }
      | (Loc.{l_value = SP.Wild; _} as p :: pats) ->
          D.Lam {
            l_src = l_src p;
            l_param = Gensym.anon_var ctr;
            l_body = go (arg_idx + 1) 0 pats;
          }
      | (Loc.{l_value = SP.Var {v_var; v_type = Some ty}; _} as p :: pats) ->
          let v = v_var.Loc.l_value in
          D.Lam {
            l_src = l_src p;
            l_param = v;
            l_body = D.Let {
                let_v = v;
                let_e =
                  D.App {
                    app_fn =
                      D.WithType {
                        wt_src = `Pattern(v_var, ty);
                        wt_type = desugar_type ty;
                      };
                    app_arg = D.Var {
                        v_var = v;
                        v_src = `Sourced v_var;
                      };
                  };
                let_body = go (arg_idx + 1) 0 pats;
              };
          }
      | (Loc.{l_value = SP.Const _; _} :: _) -> incomplete_pattern ()
      | (Loc.{l_value = SP.Ctor{c_lbl; c_arg; _}; _} as p :: pats) ->
          let v = Gensym.anon_var ctr in
          D.Match {
            m_src = l_src p;
            m_branch = D.BLabel {
                lm_default = None;
                lm_cases = Map.singleton (module Label)
                    c_lbl.Loc.l_value
                    D.(BLeaf {
                        lf_var = Some v;
                        lf_body = D.App {
                            app_fn = go arg_idx (pat_depth + 1) (c_arg :: pats);
                            app_arg = D.Var {
                                v_var = v;
                                v_src = `Generated;
                              }
                          }
                      });
              };
          }
  in
  go 0 0 ps
and desugar_record fields =
  let types, values =
    List.fold_right fields ~init:([], []) ~f:(fun bind (types, values) ->
      match bind.Loc.l_value with
      | `Value (l, ty, e) ->
          ( types
          , ((Ast.var_of_label l.Loc.l_value
             , Option.map ty ~f:desugar_type
             , desugar e
          ) :: values)
          )
      | `Type (l, params, body) ->
          ( ( desugar_type_binding (SC.var_of_label l, params, body)
              :: types
            )
          , values
          )
    )
  in
  let types = sort_let_types types in
  let binds = D.{
      rec_types = types;
      rec_vals = values;
    }
  in
  D.Record binds
and desugar_match cases =
  begin match cases with
    | (Loc.{l_value = SP.Ctor _; _}, _) :: _ ->
        desugar_lbl_match (Map.empty (module Label)) cases
    | (Loc.{l_value = SP.Const _; _}, _) :: _ ->
        desugar_const_match (Map.empty (module Const)) cases
    | [Loc.{l_value = SP.Wild; _}, body] ->
        D.BLeaf {
          lf_var = None;
          lf_body = desugar body;
        }
    | [Loc.{l_value = SP.Var{v_var = {l_value; _}; _}; _}, body] ->
        (* FIXME: Don't drop the type annotation *)
        D.BLeaf {
          lf_var = Some l_value;
          lf_body = desugar body;
        }
    | [] -> D.BLabel {
        lm_cases = Map.empty (module Label);
        lm_default = None;
      }
    | (Loc.{l_value = SP.Wild; _}, _) :: cs | (Loc.{l_value = SP.Var _; _}, _) :: cs ->
        unreachable_cases cs
  end
and desugar_const_match dict = function
  | [] -> D.BConst {
      cm_default = None;
      cm_cases = dict;
    }
  | [Loc.{l_value = SP.Wild; _}, body] -> D.BConst {
      cm_default = Some D.{
          lf_var = None;
          lf_body = desugar body;
        };
      cm_cases = dict;
    }
  | (Loc.{l_value = SP.Wild; _}, _) :: cs ->
      unreachable_cases cs
  | [Loc.{l_value = (SP.Var {v_var = {l_value; _}; v_type = _}); _}, body] ->
      (* FIXME: Don't drop the type annotation *)
      D.BConst {
        cm_default = Some D.{
            lf_var = Some l_value;
            lf_body = desugar body;
          };
        cm_cases = dict;
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
  | (Loc.{l_value = SP.Ctor _; _} as p, _) :: _ ->
      MuleErr.throw (`MatchDesugarMismatch p)
and desugar_lbl_match dict = function
  | [] -> D.BLabel {
      lm_default = None;
      lm_cases = finalize_dict dict;
    }
  | [(Loc.{l_value = SP.Wild; _}, body)] -> D.BLabel {
      lm_default = Some {
          lf_var = None;
          lf_body = desugar body;
        };
      lm_cases = finalize_dict dict;
    }
  | [Loc.{l_value = SP.Var {v_var = v; v_type = None; _}; _}, body] ->
      D.BLabel {
        lm_default = Some D.{
            lf_var = Some v.Loc.l_value;
            lf_body = desugar body;
          };
        lm_cases = finalize_dict dict;
      }
  | [Loc.{l_value = SP.Var {v_var = v; v_type = Some ty}; _}, body] ->
      let v' = Gensym.anon_var Gensym.global in
      let let_ = D.Let {
          let_v = v.Loc.l_value;
          let_e =
            D.App {
              app_fn = D.WithType {
                  wt_src = `Pattern(v, ty);
                  wt_type = desugar_type ty
                };
              app_arg = D.Var {
                  v_var = v';
                  v_src = `Generated;
                };
            };
          let_body = desugar body;
        }
      in
      D.BLabel {
        lm_default = Some{lf_var = Some v'; lf_body = let_};
        lm_cases = finalize_dict dict;
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
  Map.map dict ~f:(fun cases -> desugar_match (List.rev cases))
and desugar_let bs body =
  (* As part of the desugaring process, we have to remove all "complex" patterns;
   * in the desugared AST, let bindings only have simple variables as patterns. *)
  let rec go vals types = function
    | [] ->
        sort_let
          ~rec_types:types
          ~rec_vals:vals
          ~letrec_body:(desugar body)
    | `BindType t :: bs ->
        let (v, ty) = desugar_type_binding t in
        go vals ((v, ty) :: types) bs
    | `BindVal (p, e) :: bs ->
        go_val_binding vals types (p.Loc.l_value, desugar e) bs

  and go_val_binding vals types (pat, e) bs = match (pat, e) with
    | (SP.Var {v_var = v; v_type; _}, e) ->
        go ((v.Loc.l_value
            , Option.map v_type ~f:(fun t ->
                (desugar_type t, `Pattern (v, t))
              )
            , e
        ) :: vals) types bs
    | ((SP.Const _), _) ->
        incomplete_pattern ()
    | (SP.Wild, e) ->
        go ((Gensym.anon_var Gensym.global, None, e) :: vals) types bs
    | (SP.Ctor{c_lbl = lbl; c_arg = pat; _}, e) ->
        let ctr = Gensym.global in
        let bind_var = Gensym.anon_var ctr in
        let match_var = Gensym.anon_var ctr in
        let bind =
          ( bind_var
          , None
          , D.App {
              app_fn =
                D.Match {
                  m_src = `Generated;
                  m_branch = D.BLabel {
                      lm_default = None;
                      lm_cases = Map.singleton (module Label) lbl.Loc.l_value D.(BLeaf {
                          lf_var = Some match_var;
                          lf_body = Var {
                              v_var = match_var;
                              v_src = `Generated;
                            }
                        });
                    };
                };
              app_arg = e;
            }
          )
        in
        go_val_binding
          (bind :: vals)
          types
          (pat.Loc.l_value, D.Var {
               v_var = bind_var;
               v_src = `Generated;
             })
          bs
  in
  go [] [] (List.map bs ~f:(fun b -> b.Loc.l_value))
and desugar_type_binding: (SC.var * SC.var list * ST.lt) -> (Ast.Var.t * DK.maybe_kind DT.t) =
  fun (v, params, ty) ->
  let vloc = v in
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
          vloc
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

let rec simplify = function
  | D.LetRec{
      letrec_binds = {
        rec_types = [];
        rec_vals = [];
      };
      letrec_body;
    } ->
      simplify letrec_body
  | e ->
      D.apply_to_kids e ~f:simplify

let desugar e = simplify (desugar e)
