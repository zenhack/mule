

module GT = Graph_types
module DE = Desugared_ast_expr_t
module DT = Desugared_ast_type_t
module UF = Union_find
module C = Constraint_t

open Common_ast

module Gen : sig
  val gen_expr : Context.t -> unit DE.t -> GT.g_node
end = struct
  let make_tyvar ctx bnd tv_kind =
    let ctr = Context.get_ctr ctx in
    Context.make_type ctx (`Free {
        tv_id = GT.Ids.Type.fresh ctr;
        tv_bound = Context.make_bound ctx bnd;
        tv_kind;
      })

  let make_tyvar_q ctx bnd kind =
    Context.with_quant ctx bnd (fun _ -> make_tyvar ctx bnd kind)

  let make_type_q ctx bnd typ =
    Context.with_quant ctx bnd (fun _ -> Context.make_type ctx typ)

  let make_kind ctx pk =
    Context.make_kind ctx GT.{
        k_prekind = Context.make_prekind ctx pk;
        k_guard = Context.make_guard ctx `Free;
      }

  let throw_unbound_var v_var v_src =
    match v_src with
    | `Sourced v ->
        MuleErr.throw (`UnboundVar v)
    | `Generated ->
        MuleErr.bug ("Unbound compiler-generated variable: " ^ Var.to_string v_var)

  let make_ctor_ty ctx ctor =
    let ty = Context.make_type ctx (`Ctor ctor) in
    let bnd = GT.{ b_target = `G (Context.get_g ctx); b_flag = `Flex } in
    Context.make_quant ctx GT.{
      q_id = Ids.Quant.fresh (Context.get_ctr ctx);
      q_bound = Context.make_bound ctx bnd;
      q_body = lazy ty;
    }

  let expand_type : Context.t -> C.polarity -> unit DT.t -> GT.quant GT.var =
    fun ctx polarity -> function
    | DT.Var {v_var; v_src; v_info = _} ->
      begin match Context.lookup_type ctx v_var with
        | None ->
            throw_unbound_var v_var v_src
        | Some (`QBound ty) ->
            ty
        | Some (`LetBound f) ->
            f polarity GT.{ b_target = `G (Context.get_g ctx); b_flag = `Flex }
      end
    | DT.Named {n_name = `Text; n_info = _} -> make_ctor_ty ctx (`Type (`Const `Text))
    | DT.Named {n_name = `Int; n_info = _} -> make_ctor_ty ctx (`Type (`Const `Int))
    | DT.Named {n_name = `Char; n_info = _} -> make_ctor_ty ctx (`Type (`Const `Char))
    | _ -> failwith "TODO: other cases in expand_type"

  let _ = expand_type (* Silence the unused variable warning. TODO: actually use it. *)

  let rec gen_expr (ctx: Context.t) (expr: unit DE.t): GT.g_node =
    Context.with_sub_g ctx (fun ctx g -> gen_expr_q ctx g expr)
  and gen_expr_q ctx g expr =
    let bnd = GT.{ b_target = `G g; b_flag = `Flex } in
    match expr with
    (* The first four of these come unmodified from {Yakobowski 2008} *)
    | DE.Var {v_var; v_src} ->
        let q_var = Context.with_quant ctx bnd (fun _ -> make_tyvar ctx bnd (make_kind ctx `Type)) in
        begin match Context.lookup_val ctx v_var with
          | None ->
              throw_unbound_var v_var v_src
          | Some binding ->
              begin match binding with
                | `LetBound g ->
                    Context.constrain ctx C.(
                        `Instance {
                          inst_super = g;
                          inst_sub = q_var;
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
          let t_ret = make_tyvar ctx bnd (make_kind ctx `Type) in
          let with_quant f = Context.with_quant ctx bnd f in
          let q_arg = make_tyvar_q ctx bnd (make_kind ctx `Type) in
          let q_fn = with_quant (fun _ -> Context.make_type ctx (`Ctor(`Type(`Fn(q_arg, q_ret))))) in
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
          let g_ret = gen_expr ctx l_body in
          let q_ret = Lazy.force (GT.GNode.get g_ret) in
          Context.with_quant ctx bnd (fun _ -> Context.make_type ctx (`Ctor(`Type(`Fn(q_param, q_ret)))))
        )
    | DE.Let {let_v; let_e; let_body} ->
        let g_e = gen_expr ctx let_e in
        Context.with_val_binding ctx let_v (`LetBound g_e) (fun ctx ->
          gen_expr_q ctx g let_body
        )

    (* Boring stuff like constant literals *)
    | DE.Const {const_val} ->
        Context.with_quant ctx bnd (fun _ -> gen_const ctx const_val)
    | DE.Embed _ ->
        Context.with_quant ctx bnd (fun _ -> Context.make_type ctx (`Ctor(`Type(`Const(`Text)))))

    | DE.Ctor {c_lbl; c_arg} ->
        let g_arg = gen_expr ctx c_arg in
        let q_head = Lazy.force (GT.GNode.get g_arg) in
        let q_tail = make_tyvar_q ctx bnd (make_kind ctx `Row) in
        make_type_q ctx bnd
          (`Ctor
              (`Type
                  (`Union
                      (make_type_q ctx bnd
                          (`Ctor(`Row(`Extend(c_lbl, q_head, q_tail))))))))
    | DE.GetField {gf_lbl; gf_record} ->
        let g_record = gen_expr ctx gf_record in

        let q_head = make_tyvar_q ctx bnd (make_kind ctx `Type) in
        let q_tail = make_tyvar_q ctx bnd (make_kind ctx `Row) in
        let q_types = make_tyvar_q ctx bnd (make_kind ctx `Row) in

        let q_record = make_type_q ctx bnd
          (`Ctor
              (`Type
                  (`Record
                    ( q_types
                    , make_type_q ctx bnd (`Ctor(`Row(`Extend(gf_lbl, q_head, q_tail))))
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

        let q_record = make_type_q ctx bnd (`Ctor(`Type(`Record(q_types, q_tail)))) in
        Context.constrain ctx C.(
            `Instance {
              inst_super = g_record;
              inst_sub = q_record;
              inst_why = `RecordUpdate(uv_record);
            }
          );
        let q_values = make_type_q ctx bnd (`Ctor(`Row(`Extend(uv_lbl, q_head, q_tail)))) in
        make_type_q ctx bnd (`Ctor(`Type(`Record(q_types, q_values))));
    | _ ->
        failwith "TODO"
  and gen_const ctx const =
    let ty = match const with
      | Const.Integer _ -> `Int
      | Const.Text _ -> `Text
      | Const.Char _ -> `Char
    in
    Context.make_type ctx (`Ctor(`Type(`Const(ty))))

end
