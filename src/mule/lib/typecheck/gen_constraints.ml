

module GT = Graph_types
module DE = Desugared_ast_expr_t
module DT = Desugared_ast_type
module UF = Union_find
module C = Constraint_t

open Common_ast

module Gen : sig
  val gen_expr : Context.t -> unit DE.t -> GT.g_node

  val with_intrinsics : Context.t -> (Context.t -> 'a) -> 'a
end = struct
  let make_tyvar ctx bnd tv_kind =
    let ctr = Context.get_ctr ctx in
    let tv_id = GT.Ids.Type.fresh ctr in
    Context.make_var ctx Context.typ (`Free {
        tv_id;
        tv_merged = Set.singleton (module GT.Ids.Type) tv_id;
        tv_bound = Context.make_var ctx Context.bound bnd;
        tv_kind;
      })

  let make_tyvar_q ctx bnd kind =
    Context.with_quant ctx bnd (fun _ -> make_tyvar ctx bnd kind)

  let make_type_q ctx bnd typ =
    Context.with_quant ctx bnd (fun _ -> Context.make_var ctx Context.typ typ)

  let make_kind ctx pk =
    Context.make_var ctx Context.kind GT.{
        k_prekind = Context.make_var ctx Context.prekind pk;
        k_guard = Context.make_var ctx Context.guard `Free;
      }

  let unbound_var v_var v_src =
    match v_src with
    | `Sourced v ->
        `UnboundVar v
    | `Generated ->
        MuleErr.bug ("Unbound compiler-generated variable: " ^ Var.to_string v_var)

  let unbound_var_poison ctx v_var v_src =
    let ctr = Context.get_ctr ctx in
    Context.error ctx (unbound_var v_var v_src);
    Context.make_var ctx Context.typ (`Poison (GT.Ids.Type.fresh ctr))

  let make_ctor_ty ctx ctor =
    let ctr = Context.get_ctr ctx in
    let ty_id = GT.Ids.Type.fresh ctr in
    Context.make_var ctx Context.typ (`Ctor (ty_id, ctor))

  (* Computes a flag for a binding edge based on a quantifier and a polarity.
     universal quantifiers are flexible in positive position, and rigid in
     negative position, while the converse is true for existential quantifiers.
  *)
  let quant_flag : DT.quantifier -> C.polarity -> GT.bound_flag =
    fun q p -> match q, p with
      | `All, `Pos -> `Flex
      | `All, `Neg -> `Rigid
      | `Exist, `Pos -> `Rigid
      | `Exist, `Neg -> `Flex

  let flip_polarity : C.polarity -> C.polarity = function
    | `Pos -> `Neg
    | `Neg -> `Pos

  let rec expand_type
    : Context.t
      -> C.polarity
      -> GT.quant GT.var
      -> unit DT.t
      -> GT.typ GT.var =
    (* [expand_type ctx polarity q_target t] converts [t] into a type graph, where:

       - Any top-level quantifiers are bound on [q_target].
       - [polarity] is used to determine how to translate quantifiers; binding edges on
         quantifiers will be computed via [quant_flag].
    *)
    (* TODO: kind constraints? *)
    fun ctx polarity q_target exp ->
    let b_target = `Q q_target in
    match exp with
    | DT.Var {v_var; v_src; v_info = _} ->
        begin match Context.lookup_type ctx v_var with
          | None ->
              unbound_var_poison ctx v_var v_src
          | Some f ->
              f v_src polarity q_target
        end
    | DT.Named {n_name = `Text; n_info = _} -> make_ctor_ty ctx (`Type (`Const `Text))
    | DT.Named {n_name = `Int; n_info = _} -> make_ctor_ty ctx (`Type (`Const `Int))
    | DT.Named {n_name = `Char; n_info = _} -> make_ctor_ty ctx (`Type (`Const `Char))
    | DT.Quant {q_quant; q_var; q_bound; q_body; q_info = _} ->
        let b_flag = quant_flag q_quant polarity in
        let bnd = GT.{ b_target; b_flag } in
        let tv = match q_bound with
          | None ->
              let kind = make_kind ctx (`Free (GT.Ids.Kind.fresh (Context.get_ctr ctx))) in
              make_tyvar ctx bnd kind
          | Some ty ->
              expand_type ctx polarity q_target ty
        in
        Context.with_type_binding ctx q_var (fun _ _ _ -> tv) begin fun ctx ->
          expand_type ctx polarity q_target q_body
        end
    | DT.Fn{ fn_param; fn_ret; fn_pvar = _; fn_info = _} ->
        (* TODO: do something with fn_pvar. *)
        let mk_branch polarity expr =
          (* We always bound the new q node flexibly; only true quantifiers should ever
             be rigidly bound. *)
          Context.with_quant ctx GT.{ b_target; b_flag = `Flex }
            begin fun q_target ->
              expand_type ctx polarity q_target expr
            end
        in
        make_ctor_ty
          ctx
          (`Type
              (`Fn
                  ( mk_branch (flip_polarity polarity) fn_param
                  , mk_branch                polarity  fn_ret
                  )
              )
          )
    | DT.Union {u_row} ->
        make_ctor_ty
          ctx
          (`Type
              (`Union
                  (Context.with_quant ctx GT.{ b_target; b_flag = `Flex }
                        begin fun q_target ->
                          expand_row ctx `Union polarity q_target u_row
                        end
                  )
              )
          )
    | DT.Record {r_types; r_values; r_info = _; r_src = _} ->
        let bnd = GT.{ b_target; b_flag = `Flex } in
        let mk_branch place row =
          Context.with_quant ctx bnd (fun q_target ->
            expand_row ctx place polarity q_target row
          )
        in
        make_ctor_ty
          ctx
          (`Type
              (`Record
                  ( mk_branch (`Record `Type) r_types
                  , mk_branch (`Record `Value) r_values
                  )
              )
          )
    | DT.App {app_fn; app_arg; app_info = _} ->
        let bnd = GT.{ b_target; b_flag = `Flex } in
        let expand_type' t =
          Context.with_quant ctx bnd (fun q_target ->
            expand_type ctx polarity q_target t
          )
        in
        Context.make_var ctx Context.typ
          (`Apply
            ( GT.Ids.Type.fresh (Context.get_ctr ctx)
            , expand_type' app_fn
            , expand_type' app_arg
            )
          )
    | DT.TypeLam {tl_param; tl_body; tl_info = _} ->
        let ctr = Context.get_ctr ctx in
        let bnd = GT.{ b_target; b_flag = `Explicit } in
        let tv_id = GT.Ids.Type.fresh ctr in
        let pk_id = GT.Ids.Kind.fresh ctr in
        let param_qv = make_tyvar_q ctx bnd (make_kind ctx (`Free pk_id)) in
        let param_tv = Lazy.force (Context.read_var ctx Context.quant param_qv).q_body in
        let body_qv =
            Context.with_type_binding ctx tl_param (fun _ _ _ -> param_tv) begin fun ctx ->
                Context.with_quant ctx bnd (fun q_target ->
                  expand_type ctx polarity q_target tl_body
                )
            end
        in
        Context.make_var ctx Context.typ
          ( `Lambda
            ( tv_id
            , param_qv
            , body_qv
            )
          )
    | DT.Recur {mu_info; mu_var; mu_body} ->
        (* XXX: maybe we should be doing this in the desugar step, instead of
           here. *)
        let new_id () = GT.Ids.Type.fresh (Context.get_ctr ctx) in
        let bnd = GT.{ b_target; b_flag = `Flex } in
        let expand_type' t =
          Context.with_quant ctx bnd (fun q_target ->
            expand_type ctx polarity q_target t
          )
        in
        let body = expand_type' (DT.TypeLam {
            tl_param = mu_var;
            tl_body = mu_body;
            tl_info = mu_info;
          })
        in
        let app_id = new_id () in
        let fix_id = new_id () in
        let fix =
          Context.with_quant ctx bnd (fun _ ->
            Context.make_var ctx Context.typ (`Fix fix_id)
          )
        in
        Context.make_var ctx Context.typ (`Apply(app_id, fix, body))
    | _ -> failwith "TODO: other cases in expand_type"
  and expand_row
    : Context.t
      -> [ `Union | `Record of [ `Type | `Value ] ]
      -> C.polarity
      -> GT.quant GT.var
      -> unit DT.row
      -> GT.typ GT.var
    = fun ctx place polarity qv DT.{row_fields; row_rest; row_info = _} ->
      let tail = match place, polarity, row_rest with
        | `Union, `Pos, None
        | `Record _, `Neg, None ->
            let kind = make_kind ctx `Row in
            make_tyvar ctx GT.{ b_target = `Q qv; b_flag = `Flex } kind
        | `Union, `Neg, None
        | `Record _, `Pos, None ->
            make_ctor_ty ctx (`Row `Empty)

        | _, _, Some r ->
            (* TODO: should we be binding this on some intermediate q node,
               e.g. the one coming from an extends node? I don't think it
               matters... *)
            let tv = expand_type ctx polarity qv r in
            let kind = make_kind ctx `Row in
            Context.constrain ctx (`HasKind C.{
                has_kind_why = `RowTail;
                has_kind_kind = kind;
                has_kind_type = tv;
              });
            tv
      in
      let bnd = GT.{ b_target = `Q qv; b_flag = `Flex } in
      let mk_field t =
        Context.with_quant ctx bnd (fun _ ->
          let tv = expand_type ctx polarity qv t in
          let kind = make_kind ctx `Type in
          Context.constrain ctx (`HasKind C.{
              has_kind_why = `RowHead;
              has_kind_kind = kind;
              has_kind_type = tv;
            });
          tv
        )
      in
      List.fold_right row_fields ~init:tail ~f:(fun (l, h) t ->
        make_ctor_ty ctx (`Row (`Extend
              ( l
              , mk_field h
              , Context.with_quant ctx bnd (fun _ -> t)
              )))
      )

  let rec gen_expr (ctx: Context.t) (expr: unit DE.t): GT.g_node =
    Context.with_sub_g ctx (fun ctx g -> gen_expr_q ctx g expr)
  and gen_expr_q ctx g expr =
    let bnd = GT.{ b_target = `G g; b_flag = `Flex } in
    match expr with
    (* The first four of these come unmodified from {Yakobowski 2008} *)
    | DE.Var {v_var; v_src} ->
        begin match Context.lookup_val ctx v_var with
          | None ->
              Context.with_quant ctx bnd (fun _ -> unbound_var_poison ctx v_var v_src)
          | Some binding ->
              let q_var = make_tyvar_q ctx bnd (make_kind ctx `Type) in
              begin match binding with
                | `LetBound (g, None) ->
                    Context.constrain ctx C.(
                        `Instance {
                          inst_super = g;
                          inst_sub = q_var;
                          inst_why = `VarUse v_src;
                        }
                      )
                | `LetBound (g, Some lbl) ->
                    let row_q = make_type_q ctx bnd (
                        `Ctor(
                          GT.Ids.Type.fresh (Context.get_ctr ctx),
                          `Row(`Extend(
                            lbl,
                            q_var,
                            make_tyvar_q ctx bnd (make_kind ctx `Row))))
                    )
                    in
                    Context.constrain ctx C.(
                        `Instance {
                          inst_super = g;
                          inst_sub = row_q;
                          inst_why = `VarUse v_src;
                        }
                      )
                | `LambdaBound (q_param, l_src) ->
                    Context.constrain ctx C.(
                        `Unify {
                          unify_super = q_param;
                          unify_sub = q_var;
                          unify_why = `VarUse(v_src, l_src);
                        }
                      )
              end;
              q_var
        end
    | DE.App {app_fn; app_arg} ->
        let g_fn = gen_expr ctx app_fn in
        let g_arg = gen_expr ctx app_arg in
        Context.with_quant ctx bnd (fun q_ret ->
          let ctr = Context.get_ctr ctx in
          let t_ret = make_tyvar ctx bnd (make_kind ctx `Type) in
          let with_quant f = Context.with_quant ctx bnd f in
          let q_arg = make_tyvar_q ctx bnd (make_kind ctx `Type) in
          let q_fn = with_quant (fun _ ->
              Context.make_var
                ctx
                Context.typ
                (`Ctor(GT.Ids.Type.fresh ctr, `Type(`Fn(q_arg, q_ret))))
            )
          in
          Context.constrain ctx C.(
              `Instance {
                inst_super = g_arg;
                inst_sub = q_arg;
                inst_why = `ParamArg(app_fn, app_arg);
              }
            );
          Context.constrain ctx C.(
              `Instance {
                inst_super = g_fn;
                inst_sub = q_fn;
                inst_why = `FnApply(app_fn);
              }
            );
          t_ret
        )
    | DE.Lam {l_param; l_body; l_src} ->
        let q_param = make_tyvar_q ctx bnd (make_kind ctx `Type) in
        Context.with_val_binding ctx l_param (`LambdaBound (q_param, l_src)) (fun ctx ->
          let ctr = Context.get_ctr ctx in
          let g_ret = gen_expr ctx l_body in
          let q_ret = Lazy.force (GT.GNode.get g_ret) in
          Context.with_quant ctx bnd (fun _ ->
            Context.make_var
              ctx
              Context.typ
              (`Ctor(GT.Ids.Type.fresh ctr, `Type(`Fn(q_param, q_ret))))
          )
        )
    | DE.Let {let_v; let_e; let_body} ->
        let g_e = gen_expr ctx let_e in
        Context.with_val_binding ctx let_v (`LetBound (g_e, None)) (fun ctx ->
          gen_expr_q ctx g let_body
        )

    (* Type coercions are just the identity function specilized to the given
       type. *)
    | DE.WithType {wt_type; wt_src = _} ->
        Context.with_quant ctx bnd (fun q ->
          let tv = expand_type ctx `Pos q (DT.Fn {
              fn_info = ();
              fn_pvar = None;
              fn_param = wt_type;
              fn_ret = wt_type;
            })
          in
          let kv = Infer_kind.infer_kind ctx tv in
          Context.constrain ctx (`UnifyKind C.{
              unify_kind_why = `WithType;
              unify_kind_super = Infer_kind.kwithg ctx `Free (Context.make_var ctx Context.prekind `Type);
              unify_kind_sub = kv;
            });
          tv
        )

    | DE.LetType{lettype_v; lettype_t; lettype_body} ->
        let expand polarity =
          Context.with_sub_g ctx (fun ctx g ->
            let bnd = GT.{ b_target = `G g; b_flag = `Flex } in
            Context.with_quant ctx bnd (fun q -> expand_type ctx polarity q lettype_t)
          )
        in
        let pos = expand `Pos in
        let neg = expand `Neg in
        let get_type v_src polarity _ =
          let pk_id = GT.Ids.Kind.fresh (Context.get_ctr ctx) in
          let qv = make_tyvar_q ctx bnd (make_kind ctx (`Free pk_id)) in
          let super = match polarity with
            | `Pos -> pos
            | `Neg -> neg
          in
          Context.constrain ctx C.(
            `Instance {
              inst_super = super;
              inst_sub = qv;
              (* TODO: do we really want to re-use VarUse here? I have
                 a vague hunch that these cases want to be different. *)
              inst_why = `VarUse v_src;
            }
          );
          Lazy.force (Context.read_var ctx Context.quant qv).q_body
        in
        Context.with_type_binding ctx lettype_v get_type begin fun ctx ->
          gen_expr_q ctx g lettype_body
        end

    (* Boring stuff like constant literals *)
    | DE.Const {const_val} ->
        Context.with_quant ctx bnd (fun _ -> gen_const ctx const_val)
    | DE.Embed _ ->
        let ctr = Context.get_ctr ctx in
        Context.with_quant ctx bnd (fun _ ->
          Context.make_var
            ctx
            Context.typ
            (`Ctor(GT.Ids.Type.fresh ctr, `Type(`Const(`Text))))
        )

    | DE.Ctor {c_lbl; c_arg} ->
        let g_arg = gen_expr ctx c_arg in
        let q_head = Lazy.force (GT.GNode.get g_arg) in
        let q_tail = make_tyvar_q ctx bnd (make_kind ctx `Row) in
        let ctr = Context.get_ctr ctx in
        make_type_q ctx bnd
          (`Ctor
              (GT.Ids.Type.fresh ctr,
               `Type
                 (`Union
                     (make_type_q ctx bnd
                         (`Ctor(GT.Ids.Type.fresh ctr,
                                `Row(`Extend(c_lbl, q_head, q_tail))))))))
    | DE.GetField {gf_lbl; gf_record} ->
        let g_record = gen_expr ctx gf_record in

        let q_head = make_tyvar_q ctx bnd (make_kind ctx `Type) in
        let q_tail = make_tyvar_q ctx bnd (make_kind ctx `Row) in
        let q_types = make_tyvar_q ctx bnd (make_kind ctx `Row) in

        let ctr = Context.get_ctr ctx in
        let q_record = make_type_q ctx bnd
            (`Ctor
                (GT.Ids.Type.fresh ctr,
                 `Type
                   (`Record
                       ( q_types
                       , make_type_q
                           ctx
                           bnd
                           (`Ctor(GT.Ids.Type.fresh ctr,
                                  `Row(`Extend(gf_lbl, q_head, q_tail))))
                       ))))
        in
        Context.constrain ctx C.(
            `Instance {
              inst_super = g_record;
              inst_sub = q_record;
              inst_why = `GetField(gf_lbl, gf_record);
            }
          );
        q_head
    | DE.UpdateVal {uv_lbl; uv_val; uv_record} ->
        let g_val = gen_expr ctx uv_val in
        let g_record = gen_expr ctx uv_record in
        let q_head = Lazy.force (GT.GNode.get g_val) in
        let q_tail = make_tyvar_q ctx bnd (make_kind ctx `Row) in
        let q_types = make_tyvar_q ctx bnd (make_kind ctx `Row) in

        let ctr = Context.get_ctr ctx in
        let q_record = make_type_q
            ctx
            bnd
            (`Ctor(GT.Ids.Type.fresh ctr,
                   `Type(`Record(q_types, q_tail))))
        in
        Context.constrain ctx C.(
            `Instance {
              inst_super = g_record;
              inst_sub = q_record;
              inst_why = `RecordUpdate(uv_record);
            }
          );
        let q_values =
          make_type_q ctx bnd (`Ctor(GT.Ids.Type.fresh ctr,
                                     `Row(`Extend(uv_lbl, q_head, q_tail))))
        in
        make_type_q ctx bnd (`Ctor(GT.Ids.Type.fresh ctr,
                                   `Type(`Record(q_types, q_values))));
    | DE.Record binds ->
        gen_rec_binds ctx g binds
    | DE.LetRec {letrec_binds; letrec_body} ->
        let record = gen_rec_binds ctx g letrec_binds in
        let rec go ctx g = function
          | [] -> gen_expr_q ctx g letrec_body
          | (v, _, _) :: binds ->
              let lbl = Label.of_string (Var.to_string v) in
              let gv =
                Context.with_sub_g ctx (fun ctx g ->
                  let ctr = Context.get_ctr ctx in
                  let bnd = GT.{ b_target = `G g; b_flag = `Flex } in
                  let q_head = make_tyvar_q ctx bnd (make_kind ctx `Type) in
                  let q_tail = make_tyvar_q ctx bnd (make_kind ctx `Row) in
                  let q_types = make_tyvar_q ctx bnd (make_kind ctx `Row) in
                  let q_values =
                    make_type_q ctx bnd (`Ctor(GT.Ids.Type.fresh ctr,
                                               `Row(`Extend(lbl, q_head, q_tail))))
                  in
                  let q_rec =
                    make_type_q ctx bnd (`Ctor(GT.Ids.Type.fresh ctr,
                                               `Type(`Record(q_types, q_values))))
                  in
                  Context.constrain ctx C.(
                      `Unify {
                        unify_super = record;
                        unify_sub = q_rec;
                        unify_why = `TODO "letrec bound variable";
                      }
                    );
                  q_head
                )
              in
              Context.with_val_binding ctx v (`LetBound(gv, Some lbl)) (fun ctx ->
                go ctx g binds
              )
        in
        go ctx g letrec_binds.rec_vals
    | _ ->
        failwith "TODO: other cases in gen_expr_q"
  and gen_rec_binds ctx g binds =
    let vals =
      (* First, fold any type annotations on the binding into
         the expression: *)
      List.map binds.rec_vals ~f:(function
        | (v, None, e) -> (v, e)
        | (v, Some t, e) ->
            ( v
            , DE.App {
                app_fn = DE.WithType {
                  wt_type = t;
                  wt_src = `Generated;
                };
                app_arg = e;
              }
            )
      )
    in
    let bnd = GT.{ b_target = `G g; b_flag = `Flex } in
    let val_qvs = List.map vals ~f:(fun (v, _) ->
        (v, make_tyvar_q ctx bnd (make_kind ctx `Type))
      )
    in
    let rec go ctx = function
      | [] -> List.map vals ~f:(fun (v, e) ->
          (v, gen_expr_q ctx g e)
        )
      | ((v, qv) :: vqs) ->
          Context.with_val_binding ctx v (`LambdaBound (qv, `Generated)) (fun ctx ->
            go ctx vqs
          )
    in
    go ctx val_qvs
    |> List.fold_left
      ~init:(Context.with_quant ctx bnd (fun _ ->
          make_ctor_ty ctx (`Row `Empty)
        ))
      ~f:(fun tt (hv, ht) ->
        Context.with_quant ctx bnd (fun _ ->
          make_ctor_ty ctx (`Row (`Extend( Label.of_string (Var.to_string hv),  ht, tt)))
        ))
    |> (fun vals ->
      Context.with_quant ctx bnd (fun _ ->
        make_ctor_ty ctx (`Type (`Record(make_tyvar_q ctx bnd (make_kind ctx `Row), vals)))
      )
    )
  and gen_const ctx const =
    let ty = match const with
      | Const.Integer _ -> `Int
      | Const.Text _ -> `Text
      | Const.Char _ -> `Char
    in
    let ctr = Context.get_ctr ctx in
    Context.make_var ctx Context.typ (`Ctor(GT.Ids.Type.fresh ctr,
                                            `Type(`Const(ty))))

  let with_intrinsics ctx f =
    let with_types =
      Map.fold
        Intrinsics.types
        ~init:f
        ~f:(fun ~key ~data f ctx ->
          let ty = DT.map data ~f:(fun _ -> ()) in
          Context.with_type_binding
            ctx
            key
            (fun _v_src polarity q_target ->
                expand_type ctx polarity q_target ty
            )
            f
        )
    in
    let with_vals =
      Map.fold
        Intrinsics.values
        ~init:with_types
        ~f:(fun ~key ~data:(ty, _) f ctx ->
          let g = Context.with_sub_g ctx (fun ctx g ->
              let bnd = GT.{ b_target = `G g; b_flag = `Flex } in
              Context.with_quant ctx bnd (fun q ->
                expand_type ctx `Pos q (DT.map ty ~f:(fun _ -> ()))
              )
            )
          in
          Context.with_val_binding
            ctx
            key
            (`LetBound (g, None))
            f
        )
    in
    with_vals ctx
end
