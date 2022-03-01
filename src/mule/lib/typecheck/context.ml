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
  ctx_errors: MuleErr.t list ref;
  ctx_constraints: C.constr list ref;
  ctx_env : C.env;

  ctx_type_v: GT.prekind GT.var Lazy.t;
  ctx_row_v: GT.prekind GT.var Lazy.t;
}

type 'a vtype = ('a Union_find.store, Stores.t) lens
include Stores.Lens

let checkpoint ctx = {
  ctx with
  ctx_uf_stores = ref (!(ctx.ctx_uf_stores));
  ctx_constraints = ref (!(ctx.ctx_constraints));
}

let with_store ctx lens f =
  let stores = !(ctx.ctx_uf_stores) in
  let (store', ret) = f (lens.get stores) in
  ctx.ctx_uf_stores := lens.set store' stores;
  ret

let make_var ctx lens v =
  with_store ctx lens (fun store ->
    Union_find.make store v
  )

let make ctr f =
  let stores = ref Stores.{
      s_quants = Union_find.new_store ();
      s_types = Union_find.new_store ();
      s_bounds = Union_find.new_store ();
      s_prekinds = Union_find.new_store ();
      s_kinds = Union_find.new_store ();
      s_guards = Union_find.new_store ();
    }
  in
  let rec ctx = lazy {
    ctx_g = GT.GNode.make_root ctr (lazy (
        Lazy.force (GT.GNode.get (f (Lazy.force ctx)))
      ));
    ctx_ctr = ctr;
    ctx_uf_stores = stores;
    ctx_constraints = ref [];
    ctx_errors = ref [];
    ctx_env = C.{
        vals = Map.empty (module Var);
        types = Map.empty (module Var);
      };
    ctx_type_v = lazy (make_var (Lazy.force ctx) prekind `Type);
    ctx_row_v = lazy (make_var (Lazy.force ctx) prekind `Row);
  }
  in
  Lazy.force ctx

let read_var ctx lens var =
  with_store ctx lens (fun store ->
    Union_find.get store var
  )


let type_v ctx = Lazy.force ctx.ctx_type_v
let row_v ctx = Lazy.force ctx.ctx_row_v

let merge ctx lens l r value =
  with_store ctx lens (fun store ->
    (Union_find.union (fun _ _ -> value) store l r, ())
  )

let var_eq ctx lens l r =
  with_store ctx lens (fun store ->
    Union_find.eq store l r
  )

let write_var ctx lens value var =
  with_store ctx lens (fun store ->
    (Union_find.set store var value, ())
  )

let modify_var ctx lens f var =
  write_var ctx lens (f (read_var ctx lens var)) var

let with_quant ctx bnd f =
  let q_id = GT.Ids.Quant.fresh ctx.ctx_ctr in
  let rec q = lazy (make_var ctx quant {
      q_id;
      q_merged = Set.singleton (module GT.Ids.Quant) q_id;
      q_bound = make_var ctx bound bnd;
      q_body;
    })
  and q_body = lazy (f (Lazy.force q))
  in
  ignore (Lazy.force q_body);
  Lazy.force q

let get_g ctx = ctx.ctx_g

let make_empty ctr = make ctr get_g

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

let take_constraints ctx =
  let ret = get_constraints ctx in
  ctx.ctx_constraints := [];
  ret

let with_val_binding ctx var value =
  let vals = Map.set ~key:var ~data:value ctx.ctx_env.vals in
  { ctx with ctx_env = { ctx.ctx_env with vals } }

let lookup_val ctx var =
  Map.find ctx.ctx_env.vals var

let with_type_binding ctx var binding =
  let types = Map.set ~key:var ~data:binding ctx.ctx_env.types in
  { ctx with ctx_env = { ctx.ctx_env with types } }

let lookup_type ctx var =
  Map.find ctx.ctx_env.types var

let error ctx err =
  ctx.ctx_errors := err :: !(ctx.ctx_errors)

let errors ctx =
  List.rev (!(ctx.ctx_errors))

module DebugGraph = struct
  type seen = {
    quant_seen: (GT.Ids.Quant.t, unit) Seen.t;
    type_seen: (GT.Ids.Type.t, unit) Seen.t;
    g_seen: (GT.Ids.G.t, unit) Seen.t;
  }

  let empty_seen () = {
    quant_seen = Seen.make (module GT.Ids.Quant);
    type_seen = Seen.make (module GT.Ids.Type);
    g_seen = Seen.make (module GT.Ids.G);
  }

  let typ_kids ctx t =
    begin match t with
      | `Free _ | `Poison _ -> []
      | `Apply(_, f, arg) -> [f; arg]
      | `Lambda(_, param, body) -> [param; body]
      | `GetField _ -> []
      | `Fix _ -> []
      | `Ctor(_, `Type(`Fn(p, r))) -> [p; r]
      | `Ctor(_, `Type(`Record(t, v))) -> [t; v]
      | `Ctor(_, `Type(`Union r)) -> [r]
      | `Ctor(_, `Type(`Const _)) -> []
      | `Ctor(_, `Row(`Empty)) -> []
      | `Ctor(_, `Row(`Extend (_, h, t))) -> [h; t]
    end
    |> List.map ~f:(read_var ctx quant)

  let rec dump_g ctx seen g =
    let id = GT.GNode.id g in
    Seen.guard seen.g_seen id (fun () ->
      let id = GT.Ids.G.to_int id in
      Debug.show_node `G id [id];
      let q_var = Lazy.force (GT.GNode.get g) in
      let q = read_var ctx quant q_var in
      dump_q ctx seen q;
      Debug.show_edge `Structural
        id
        (GT.Ids.Quant.to_int q.q_id);
      Option.iter
        (GT.GNode.bound g)
        ~f:(fun g_bound ->
          dump_g ctx seen g_bound;
          Debug.show_edge (`Binding `Flex)
            (GT.Ids.G.to_int (GT.GNode.id g_bound))
            (GT.Ids.G.to_int (GT.GNode.id g))
        )
    )
  and dump_q ctx seen q =
    let id = q.q_id in
    Seen.guard seen.quant_seen id (fun () ->
      let q_id = GT.Ids.Quant.to_int id in
      let q_merged = Set.to_list q.q_merged
                   |> List.map ~f:GT.Ids.Quant.to_int
      in
      Debug.show_node `Quant q_id q_merged;
      let t_var = Lazy.force q.q_body in
      let t = read_var ctx typ t_var in
      dump_typ ctx seen t;
      let t_id = GT.typ_id t in
      Debug.show_edge `Structural
        q_id
        (GT.Ids.Type.to_int t_id);
      dump_bound ctx seen q_id (read_var ctx bound q.q_bound)
    )
  and dump_bound ctx seen src b =
    (* We don't need to track bounds in `seen`, since they're non-cyclic
       and we already track their sources. *)
    let dest =  match b.GT.b_target with
      | `G g ->
          dump_g ctx seen g;
          GT.Ids.G.to_int (GT.GNode.id g)
      | `Q qv ->
          let q = read_var ctx quant qv in
          dump_q ctx seen q;
          GT.Ids.Quant.to_int q.q_id
    in
    Debug.show_edge (`Binding b.GT.b_flag) dest src
  and merged_typ_ids t = match t with
    | `Free GT.{tv_merged; _} -> Set.to_list tv_merged
    | _ -> [GT.typ_id t]
  and dump_typ ctx seen t =
    let id = GT.typ_id t in
    Seen.guard seen.type_seen id (fun () ->
      let node_type = match t with
        | `Free {tv_bound; _} ->
            dump_bound ctx seen
              (GT.Ids.Type.to_int id)
              (read_var ctx bound tv_bound);
            `Free
        | `Ctor(_, `Row(`Extend(lbl, _, _))) -> `Const (`Extend lbl)
        | `Ctor(_, `Row `Empty) -> `Const (`Named `Empty)
        | `Ctor(_, `Type t) -> `Const (`Named (match t with
            | `Const `Text -> `Text
            | `Const `Int -> `Int
            | `Const `Char -> `Char
            | `Fn _ -> `Fn
            | `Record _ -> `Record
            | `Union _ -> `Union
          ))
        | `GetField (_, section, lbl) -> `Const(`Named(`GetField(section, lbl)))
        | `Lambda _ -> `Const (`Named `Lambda)
        | `Apply _ -> `Const (`Named `Apply)
        | `Fix _ -> `Const (`Named `Fix)
        | `Poison _ -> `Const (`Named `Poison)
      in
      Debug.show_node node_type
        (GT.Ids.Type.to_int id)
        (List.map ~f:GT.Ids.Type.to_int (merged_typ_ids t));
      let kids = typ_kids ctx t in
      List.iter kids ~f:(fun q ->
        dump_q ctx seen q;
        Debug.show_edge `Structural
          (GT.Ids.Type.to_int id)
          (GT.Ids.Quant.to_int q.q_id)
      );
      begin match kids with
        | [] -> ()
        | q :: qs ->
            ignore (List.fold_left qs ~init:q ~f:(fun l r ->
                Debug.show_edge `Sibling
                  (GT.Ids.Quant.to_int l.q_id)
                  (GT.Ids.Quant.to_int r.q_id);
                r
              ))
      end
    )

  let dump ctx extra_constraints =
    let seen = empty_seen () in
    Debug.start_graph ();
    dump_g ctx seen (get_g ctx);
    List.iter (extra_constraints @ get_constraints ctx) ~f:(function
      | `Instance C.{inst_super; inst_sub; inst_why = _} ->
          dump_g ctx seen inst_super;
          let q = read_var ctx quant inst_sub in
          dump_q ctx seen q;
          let q_id = GT.Ids.Quant.to_int q.q_id in
          let g_id = GT.Ids.G.to_int (GT.GNode.id inst_super) in
          Debug.show_edge `Instance g_id q_id
      | `Unify C.{unify_super; unify_sub; unify_why = _} ->
          let q_super = read_var ctx quant unify_super in
          let q_sub = read_var ctx quant unify_sub in
          dump_q ctx seen q_super;
          dump_q ctx seen q_sub;
          Debug.show_edge `Unify
            (GT.Ids.Quant.to_int q_super.q_id)
            (GT.Ids.Quant.to_int q_sub.q_id)
      | _ -> ()
    );
    Debug.end_graph ()
end
