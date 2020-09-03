module GT = Graph_types
module C = Constraint_t

open Common_ast

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
    let quant = {
      get = (fun s -> s.s_quants );
      set = (fun s_quants s -> { s with s_quants });
    }

    let typ = {
      get = (fun s -> s.s_types);
      set = (fun s_types s -> { s with s_types });
    }

    let bound = {
      get = (fun s -> s.s_bounds);
      set = (fun s_bounds s -> { s with s_bounds });
    }

    let prekind = {
      get = (fun s -> s.s_prekinds);
      set = (fun s_prekinds s -> { s with s_prekinds });
    }

    let kind = {
      get = (fun s -> s.s_kinds);
      set = (fun s_kinds s -> { s with s_kinds });
    }

    let guard = {
      get = (fun s -> s.s_guards);
      set = (fun s_guards s -> { s with s_guards });
    }
  end
end

type t = {
  ctx_g: GT.g_node;
  ctx_ctr: Gensym.counter;
  ctx_uf_stores: Stores.t ref;
  ctx_constraints: C.constr list ref;
  ctx_env : C.env;
}

type 'a vtype = ('a Union_find.store, Stores.t) lens
include Stores.Lens

let make ctr f =
  let rec ctx = lazy {
    ctx_g = GT.GNode.make_root ctr (lazy (
        Lazy.force (GT.GNode.get (f (Lazy.force ctx)))
      ));
    ctx_ctr = ctr;
    ctx_uf_stores = ref Stores.{
        s_quants = Union_find.new_store ();
        s_types = Union_find.new_store ();
        s_bounds = Union_find.new_store ();
        s_prekinds = Union_find.new_store ();
        s_kinds = Union_find.new_store ();
        s_guards = Union_find.new_store ();
      };
    ctx_constraints = ref [];
    ctx_env = C.{
        vals = Map.empty (module Var);
        types = Map.empty (module Var);
      };
  }
  in
  Lazy.force ctx

let checkpoint ctx = {
  ctx with
  ctx_uf_stores = ref (!(ctx.ctx_uf_stores));
  ctx_constraints = ref (!(ctx.ctx_constraints));
}

let make_var ctx lens v =
  let stores = !(ctx.ctx_uf_stores) in
  let (store', var) = Union_find.make (lens.get stores) v in
  ctx.ctx_uf_stores := lens.set store' stores;
  var

let read_var ctx lens var =
  let stores = !(ctx.ctx_uf_stores) in
  let store = lens.get stores in
  let (store', value) = Union_find.get store var in
  ctx.ctx_uf_stores := lens.set store' stores;
  value

let write_var ctx lens value var =
  let stores = !(ctx.ctx_uf_stores) in
  ctx.ctx_uf_stores := lens.set (Union_find.set (lens.get stores) var value) stores

let with_quant ctx bnd f =
  let q_id = GT.Ids.Quant.fresh ctx.ctx_ctr in
  let rec q = lazy (make_var ctx quant {
      q_id;
      q_bound = make_var ctx bound bnd;
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

let get_constraints ctx =
  !(ctx.ctx_constraints)

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


module DebugGraph = struct
  type seen = {
    quant_seen: GT.Ids.QuantSet.t ref;
    type_seen: GT.Ids.TypeSet.t ref;
    g_seen: GT.Ids.GSet.t ref;
  }

  let empty_seen () = {
    quant_seen = ref (Set.empty (module GT.Ids.Quant));
    type_seen = ref (Set.empty (module GT.Ids.Type));
    g_seen = ref (Set.empty (module GT.Ids.G));
  }

  let rec dump_g ctx seen g =
    let id = GT.GNode.id g in
    let g_seen = !(seen.g_seen) in
    if not (Set.mem g_seen id) then
      begin
        seen.g_seen := Set.add g_seen id;
        Debug.show_node `G (GT.Ids.G.to_int id);
        let q_var = Lazy.force (GT.GNode.get g) in
        let q = read_var ctx quant q_var in
        dump_q ctx seen q;
        Debug.show_edge `Structural
          (GT.Ids.G.to_int id)
          (GT.Ids.Quant.to_int q.q_id);
      end
  and dump_q ctx seen q =
    let id = q.q_id in
    let quant_seen = !(seen.quant_seen) in
    if not (Set.mem quant_seen id) then
      begin
        seen.quant_seen := Set.add quant_seen id;
        Debug.show_node `Quant (GT.Ids.Quant.to_int id);
        let t_var = Lazy.force q.q_body in
        let t = read_var ctx typ t_var in
        dump_typ ctx seen t
      end
  and dump_typ _ctx _seen _t =
    failwith "TODO"

  let dump ctx =
    let seen = empty_seen () in
    Debug.start_graph ();
    List.iter (get_constraints ctx) ~f:(function
      | `Instance C.{inst_super; _} -> dump_g ctx seen inst_super
      | _ -> ()
    );
    Debug.end_graph ()
end
