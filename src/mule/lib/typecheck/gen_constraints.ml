

module GT = Graph_types
module DE = Desugared_ast_expr_t
module UF = Union_find

module type M_sig = sig
  type ctx

  val make_quant : ctx -> GT.quant -> GT.quant GT.var
  val make_type : ctx -> GT.typ -> GT.typ GT.var
  val make_kind : ctx -> GT.kind -> GT.kind GT.var
  val make_tbound : ctx -> GT.tbound -> GT.tbound GT.var
  val make_qbound : ctx -> GT.qbound -> GT.qbound GT.var

  val with_quant : ctx -> GT.qbound -> (GT.quant GT.var -> GT.typ GT.var) -> GT.quant GT.var
  val with_sub_g : ctx -> (ctx -> GT.g_node -> GT.quant GT.var) -> GT.g_node

  val get_ctr : ctx -> Gensym.counter
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
      s_tbounds: GT.tbound Union_find.store;
      s_qbounds: GT.qbound Union_find.store;
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

      let tbounds = {
        get = (fun s -> s.s_tbounds);
        set = (fun s_tbounds s -> { s with s_tbounds });
      }

      let qbounds = {
        get = (fun s -> s.s_qbounds);
        set = (fun s_qbounds s -> { s with s_qbounds });
      }
    end
  end

  type ctx = {
    ctx_g: GT.g_node;
    ctx_ctr: Gensym.counter;
    ctx_uf_stores: Stores.t ref;
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

  let make_tbound ctx v =
    make_var ctx Stores.Lens.tbounds v

  let make_qbound ctx v =
    make_var ctx Stores.Lens.qbounds v

  let with_quant ctx bnd f =
    let q_id = GT.Ids.Quant.fresh ctx.ctx_ctr in
    let rec q = lazy (make_quant ctx {
      q_id;
      q_bound = make_qbound ctx bnd;
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
end

module Gen : sig
  val gen_expr : M.ctx -> 'a DE.t -> GT.g_node
end = struct
  let flex_var ctx q =
    let ctr = M.get_ctr ctx in
    M.make_type ctx (`Free {
      tv_id = GT.Ids.Type.fresh ctr;
      tv_bound = M.make_tbound ctx {
        b_target = q;
        b_flag = `Flex;
      };
    })

  let rec gen_expr ctx = function
    | DE.App {app_fn; app_arg} -> M.with_sub_g ctx (fun ctx g ->
        let _g_fn = gen_expr ctx app_fn in
        let _g_arg = gen_expr ctx app_arg in
        M.with_quant ctx GT.{ b_target = `G g; b_flag = `Flex } (fun q ->
          let bnd = GT.{ b_target = `Q q; b_flag = `Flex } in
          let q_arg = M.with_quant ctx bnd (fun _ -> flex_var ctx q) in
          let q_ret = M.with_quant ctx bnd (fun _ -> flex_var ctx q) in
          let t_fn = M.make_type ctx (`Lambda(q_arg, q_ret)) in
          (* TODO: add instance constraints. *)
          t_fn
        )
      )
    | _ ->
        failwith "TODO"
end
