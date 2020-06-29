

module GT = Graph_types
module DE = Desugared_ast_expr_t
module UF = Union_find
module C = Constraint_t

open Common_ast

type var_binding =
  [ `Lambda of
      ( GT.quant GT.var
      * DE.lam_src
      )
  | `Let of GT.g_node
  ]

module type M_sig = sig
  type ctx

  val make_quant : ctx -> GT.quant -> GT.quant GT.var
  val make_type : ctx -> GT.typ -> GT.typ GT.var
  val make_kind : ctx -> GT.kind -> GT.kind GT.var
  val make_bound : ctx -> GT.bound -> GT.bound GT.var

  val with_quant : ctx -> GT.bound -> (GT.quant GT.var -> GT.typ GT.var) -> GT.quant GT.var
  val with_sub_g : ctx -> (ctx -> GT.g_node -> GT.quant GT.var) -> GT.g_node

  val with_binding : ctx -> Var.t -> var_binding -> (ctx -> 'a) -> 'a
  val lookup_var : ctx -> Var.t -> var_binding option

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
      s_kinds: GT.kind Union_find.store;
      s_types: GT.typ Union_find.store;
      s_bounds: GT.bound Union_find.store;
    }

    module Lens = struct
      (* TODO(cleanup): auto-generate these somehow. *)
      let quants = {
        get = (fun s -> s.s_quants );
        set = (fun s_quants s -> { s with s_quants });
      }

      let kinds = {
        get = (fun s -> s.s_kinds);
        set = (fun s_kinds s -> { s with s_kinds });
      }

      let types = {
        get = (fun s -> s.s_types);
        set = (fun s_types s -> { s with s_types });
      }

      let bounds = {
        get = (fun s -> s.s_bounds);
        set = (fun s_bounds s -> { s with s_bounds });
      }
    end
  end

  type ctx = {
    ctx_g: GT.g_node;
    ctx_ctr: Gensym.counter;
    ctx_uf_stores: Stores.t ref;
    ctx_constraints: C.constr list ref;
    ctx_vars: var_binding VarMap.t;
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

  let make_kind ctx v =
    make_var ctx Stores.Lens.kinds v

  let make_bound ctx v =
    make_var ctx Stores.Lens.bounds v

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

  let with_binding ctx var value f =
    f { ctx with ctx_vars = Map.set ~key:var ~data:value ctx.ctx_vars }

  let lookup_var ctx var =
    Map.find ctx.ctx_vars var
end

module Gen : sig
  val gen_expr : M.ctx -> unit DE.t -> GT.g_node
end = struct
  let make_tyvar ctx bnd =
    let ctr = M.get_ctr ctx in
    M.make_type ctx (`Free {
      tv_id = GT.Ids.Type.fresh ctr;
      tv_bound = M.make_bound ctx bnd;
    })

  let rec gen_expr (ctx: M.ctx) (expr: unit DE.t): GT.g_node =
    M.with_sub_g ctx (fun ctx g -> gen_expr_q ctx g expr)
  and gen_expr_q ctx g expr = match expr with
    (* The first four of these come unmodified from {Yakobowski 2008} *)
    | DE.Var {v_var; v_src} ->
        let bnd = GT.{ b_target = `G g; b_flag = `Flex } in
        let q_var = M.with_quant ctx bnd (fun _ -> make_tyvar ctx bnd) in
        begin match M.lookup_var ctx v_var with
          | Some binding ->
              begin match binding with
                | `Let g ->
                    M.constrain ctx (`Instance (g, q_var, `VarUse v_src))
                | `Lambda (q_param, l_src) ->
                    M.constrain ctx (`Unify(q_param, q_var, `VarUse(v_src, l_src)))
              end;
              q_var
          | None ->
              begin match v_src with
                | `Sourced v ->
                    MuleErr.throw (`UnboundVar v)
                | `Generated ->
                    MuleErr.bug ("Unbound compiler-generated variable: " ^ Var.to_string v_var)
              end
        end
    | DE.App {app_fn; app_arg} ->
        let g_fn = gen_expr ctx app_fn in
        let g_arg = gen_expr ctx app_arg in
        let bnd = GT.{ b_target = `G g; b_flag = `Flex } in
        M.with_quant ctx bnd (fun q_ret ->
          let t_ret = make_tyvar ctx bnd in
          let with_quant f = M.with_quant ctx bnd f in
          let q_arg = with_quant (fun _ -> make_tyvar ctx bnd) in
          let q_fn = with_quant (fun _ -> M.make_type ctx (`Ctor(`Type(`Fn(q_arg, q_ret))))) in
          M.constrain ctx (`Instance (g_arg, q_arg, `ParamArg(app_fn, app_arg)));
          M.constrain ctx (`Instance (g_fn, q_fn, `FnApply(app_fn)));
          t_ret
        )
    | DE.Lam {l_param; l_body; l_src} ->
        let bnd = GT.{ b_target = `G g; b_flag = `Flex } in
        let q_param = M.with_quant ctx bnd (fun _ -> make_tyvar ctx bnd) in
        M.with_binding ctx l_param (`Lambda (q_param, l_src)) (fun ctx ->
          let g_ret = gen_expr ctx l_body in
          let q_ret = Lazy.force (GT.GNode.get g_ret) in
          M.with_quant ctx bnd (fun _ -> M.make_type ctx (`Ctor(`Type(`Fn(q_param, q_ret)))))
      )
    | DE.Let {let_v; let_e; let_body} ->
        let g_e = gen_expr ctx let_e in
        M.with_binding ctx let_v (`Let g_e) (fun ctx ->
          gen_expr_q ctx g let_body
        )
    | _ ->
        failwith "TODO"
end
