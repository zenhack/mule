

module GT = Graph_types
module DE = Desugared_ast_expr_t
module DT = Desugared_ast_type_t
module UF = Union_find
module C = Constraint_t

open Common_ast

module type M_sig = sig
  type ctx

  val make_quant : ctx -> GT.quant -> GT.quant GT.var
  val make_type : ctx -> GT.typ -> GT.typ GT.var
  val make_bound : ctx -> GT.bound -> GT.bound GT.var

  val make_kind : ctx -> GT.kind -> GT.kind GT.var
  val make_prekind : ctx -> GT.prekind -> GT.prekind GT.var
  val make_guard : ctx -> GT.guard -> GT.guard GT.var

  val with_quant : ctx -> GT.bound -> (GT.quant GT.var -> GT.typ GT.var) -> GT.quant GT.var
  val with_sub_g : ctx -> (ctx -> GT.g_node -> GT.quant GT.var) -> GT.g_node

  val get_g : ctx -> GT.g_node

  val with_val_binding : ctx -> Var.t -> C.val_var -> (ctx -> 'a) -> 'a
  val lookup_val : ctx -> Var.t -> C.val_var option

  val with_type_binding : ctx -> Var.t -> C.type_var -> (ctx -> 'a) -> 'a
  val lookup_type : ctx -> Var.t -> C.type_var option

  val get_ctr : ctx -> Gensym.counter

  val constrain : ctx -> C.constr -> unit
end

module M : M_sig = struct
  type ('item, 'container) lens = {
    get : 'container -> 'item;
    set : 'item -> 'container -> 'container;
  }

  module Stores = struct
    type t = {
      s_quants: GT.quant Union_find.store;
      s_types: GT.typ Union_find.store;
      s_bounds: GT.bound Union_find.store;
      s_prekinds: GT.prekind Union_find.store;
      s_kinds: GT.kind Union_find.store;
      s_guards: GT.guard Union_find.store;
    }

    module Lens = struct
      (* TODO(cleanup): auto-generate these somehow. *)
      let quants = {
        get = (fun s -> s.s_quants );
        set = (fun s_quants s -> { s with s_quants });
      }

      let types = {
        get = (fun s -> s.s_types);
        set = (fun s_types s -> { s with s_types });
      }

      let bounds = {
        get = (fun s -> s.s_bounds);
        set = (fun s_bounds s -> { s with s_bounds });
      }

      let prekinds = {
        get = (fun s -> s.s_prekinds);
        set = (fun s_prekinds s -> { s with s_prekinds });
      }

      let kinds = {
        get = (fun s -> s.s_kinds);
        set = (fun s_kinds s -> { s with s_kinds });
      }

      let guards = {
        get = (fun s -> s.s_guards);
        set = (fun s_guards s -> { s with s_guards });
      }
    end
  end

  type ctx = {
    ctx_g: GT.g_node;
    ctx_ctr: Gensym.counter;
    ctx_uf_stores: Stores.t ref;
    ctx_constraints: C.constr list ref;
    ctx_env : C.env;
  }

  let make_var ctx lens v =
    let stores = !(ctx.ctx_uf_stores) in
    let (store', var) = Union_find.make (lens.get stores) v in
    ctx.ctx_uf_stores := lens.set store' stores;
    var

  let make_quant ctx v =
    make_var ctx Stores.Lens.quants v

  let make_type ctx v =
    make_var ctx Stores.Lens.types v

  let make_bound ctx v =
    make_var ctx Stores.Lens.bounds v

  let make_prekind ctx v =
    make_var ctx Stores.Lens.prekinds v

  let make_kind ctx v =
    make_var ctx Stores.Lens.kinds v

  let make_guard ctx v =
    make_var ctx Stores.Lens.guards v

  let with_quant ctx bnd f =
    let q_id = GT.Ids.Quant.fresh ctx.ctx_ctr in
    let rec q = lazy (make_quant ctx {
        q_id;
        q_bound = make_bound ctx bnd;
        q_body;
      })
    and q_body = lazy (f (Lazy.force q))
    in
    ignore (Lazy.force q_body);
    Lazy.force q

  let get_g ctx = ctx.ctx_g

  let with_sub_g ctx f =
    let rec g = lazy (GT.GNode.make_child ctx.ctx_g qvar)
    and qvar = lazy (
      let g = Lazy.force g in
      f { ctx with ctx_g = g } g
    )
    in
    ignore (Lazy.force qvar);
    Lazy.force g

  let get_ctr c =
    c.ctx_ctr

  let constrain ctx c =
    let cs = ctx.ctx_constraints in
    cs := (c :: !cs)

  let with_val_binding ctx var value f =
    let vals = Map.set ~key:var ~data:value ctx.ctx_env.vals in
    f { ctx with ctx_env = { ctx.ctx_env with vals } }

  let lookup_val ctx var =
    Map.find ctx.ctx_env.vals var

  let with_type_binding ctx var binding f =
    let types = Map.set ~key:var ~data:binding ctx.ctx_env.types in
    f { ctx with ctx_env = { ctx.ctx_env with types } }

  let lookup_type ctx var =
    Map.find ctx.ctx_env.types var
end

module Gen : sig
  val gen_expr : M.ctx -> unit DE.t -> GT.g_node
end = struct
  let make_tyvar ctx bnd tv_kind =
    let ctr = M.get_ctr ctx in
    M.make_type ctx (`Free {
        tv_id = GT.Ids.Type.fresh ctr;
        tv_bound = M.make_bound ctx bnd;
        tv_kind;
      })

  let make_tyvar_q ctx bnd kind =
    M.with_quant ctx bnd (fun _ -> make_tyvar ctx bnd kind)

  let make_type_q ctx bnd typ =
    M.with_quant ctx bnd (fun _ -> M.make_type ctx typ)

  let make_kind ctx pk =
    M.make_kind ctx GT.{
        k_prekind = M.make_prekind ctx pk;
        k_guard = M.make_guard ctx `Free;
      }

  let throw_unbound_var v_var v_src =
    match v_src with
    | `Sourced v ->
        MuleErr.throw (`UnboundVar v)
    | `Generated ->
        MuleErr.bug ("Unbound compiler-generated variable: " ^ Var.to_string v_var)

  let make_ctor_ty ctx ctor =
    let ty = M.make_type ctx (`Ctor ctor) in
    let bnd = GT.{ b_target = `G (M.get_g ctx); b_flag = `Flex } in
    M.make_quant ctx GT.{
      q_id = Ids.Quant.fresh (M.get_ctr ctx);
      q_bound = M.make_bound ctx bnd;
      q_body = lazy ty;
    }

  let expand_type : M.ctx -> C.polarity -> unit DT.t -> GT.quant GT.var =
    fun ctx polarity -> function
    | DT.Var {v_var; v_src; v_info = _} ->
      begin match M.lookup_type ctx v_var with
        | None ->
            throw_unbound_var v_var v_src
        | Some (`QBound ty) ->
            ty
        | Some (`LetBound f) ->
            f polarity GT.{ b_target = `G (M.get_g ctx); b_flag = `Flex }
      end
    | DT.Named {n_name = `Text; n_info = _} -> make_ctor_ty ctx (`Type (`Const `Text))
    | DT.Named {n_name = `Int; n_info = _} -> make_ctor_ty ctx (`Type (`Const `Int))
    | DT.Named {n_name = `Char; n_info = _} -> make_ctor_ty ctx (`Type (`Const `Char))
    | _ -> failwith "TODO: other cases in expand_type"

  let _ = expand_type (* Silence the unused variable warning. TODO: actually use it. *)

  let rec gen_expr (ctx: M.ctx) (expr: unit DE.t): GT.g_node =
    M.with_sub_g ctx (fun ctx g -> gen_expr_q ctx g expr)
  and gen_expr_q ctx g expr =
    let bnd = GT.{ b_target = `G g; b_flag = `Flex } in
    match expr with
    (* The first four of these come unmodified from {Yakobowski 2008} *)
    | DE.Var {v_var; v_src} ->
        let q_var = M.with_quant ctx bnd (fun _ -> make_tyvar ctx bnd (make_kind ctx `Type)) in
        begin match M.lookup_val ctx v_var with
          | None ->
              throw_unbound_var v_var v_src
          | Some binding ->
              begin match binding with
                | `LetBound g ->
                    M.constrain ctx (`Instance (g, q_var, `VarUse v_src))
                | `LambdaBound (q_param, l_src) ->
                    M.constrain ctx (`Unify(q_param, q_var, `VarUse(v_src, l_src)))
              end;
              q_var
        end
    | DE.App {app_fn; app_arg} ->
        let g_fn = gen_expr ctx app_fn in
        let g_arg = gen_expr ctx app_arg in
        M.with_quant ctx bnd (fun q_ret ->
          let t_ret = make_tyvar ctx bnd (make_kind ctx `Type) in
          let with_quant f = M.with_quant ctx bnd f in
          let q_arg = make_tyvar_q ctx bnd (make_kind ctx `Type) in
          let q_fn = with_quant (fun _ -> M.make_type ctx (`Ctor(`Type(`Fn(q_arg, q_ret))))) in
          M.constrain ctx (`Instance (g_arg, q_arg, `ParamArg(app_fn, app_arg)));
          M.constrain ctx (`Instance (g_fn, q_fn, `FnApply(app_fn)));
          t_ret
        )
    | DE.Lam {l_param; l_body; l_src} ->
        let q_param = make_tyvar_q ctx bnd (make_kind ctx `Type) in
        M.with_val_binding ctx l_param (`LambdaBound (q_param, l_src)) (fun ctx ->
          let g_ret = gen_expr ctx l_body in
          let q_ret = Lazy.force (GT.GNode.get g_ret) in
          M.with_quant ctx bnd (fun _ -> M.make_type ctx (`Ctor(`Type(`Fn(q_param, q_ret)))))
        )
    | DE.Let {let_v; let_e; let_body} ->
        let g_e = gen_expr ctx let_e in
        M.with_val_binding ctx let_v (`LetBound g_e) (fun ctx ->
          gen_expr_q ctx g let_body
        )

    (* Boring stuff like constant literals *)
    | DE.Const {const_val} ->
        M.with_quant ctx bnd (fun _ -> gen_const ctx const_val)
    | DE.Embed _ ->
        M.with_quant ctx bnd (fun _ -> M.make_type ctx (`Ctor(`Type(`Const(`Text)))))

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
        M.constrain ctx (`Instance(g_record, q_record, `GetField(gf_lbl, gf_record)));
        q_head
    | DE.UpdateVal {uv_lbl; uv_val; uv_record} ->
        let g_val = gen_expr ctx uv_val in
        let g_record = gen_expr ctx uv_record in
        let q_head = Lazy.force (GT.GNode.get g_val) in
        let q_tail = make_tyvar_q ctx bnd (make_kind ctx `Row) in
        let q_types = make_tyvar_q ctx bnd (make_kind ctx `Row) in

        let q_record = make_type_q ctx bnd (`Ctor(`Type(`Record(q_types, q_tail)))) in
        M.constrain ctx (`Instance(g_record, q_record, `RecordUpdate(uv_record)));
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
    M.make_type ctx (`Ctor(`Type(`Const(ty))))

end
