(* This module is responsible for turning a graphical type
   into a syntactic one.

   We borrow and extend a trick from {QMLF}: the authors observe
   that type variables that are used only once, and are either flexible
   in positive position or rigid in negative position can be inlined,
   reducing the need to use the bounded-quantification syntax.

   Our extension is that, since mule also has existential quantifiers,
   we can use those for rigid variables in positive position or flexible
   variables in negative position -- so the bounded quantification syntax
   is only necessary when the type is truly inexpressible as a tree.

   Much of the logic in this module has to do with preparation; e.g.
   we first compute reference counts for each type, so we can easily
   tell whether we should inline a type.
*)

module GT = Graph_types
module DT = Desugared_ast_type_t
module Var = Common_ast.Var

type rc = {
  rc_q: int GT.Ids.QuantMap.t;
  rc_ty: int GT.Ids.TypeMap.t;
}

let empty_rcs = {
  rc_q = Map.empty (module GT.Ids.Quant);
  rc_ty = Map.empty (module GT.Ids.Type);
}

let addref_q rc id =
  Ref.replace rc (fun r ->
    { r with rc_q = Map.update r.rc_q id ~f:(fun v -> Option.value v ~default:0 + 1) }
  )

let addref_ty rc id =
  Ref.replace rc (fun r ->
    { r with rc_ty = Map.update r.rc_ty id ~f:(fun v -> Option.value v ~default:0 + 1) }
  )

let rec compute_rcs_q seen ctx rc qv =
  let q = Context.read_var ctx Context.quant qv in
  addref_q rc q.q_id;
  Seen.guard seen.GT.seen_q q.q_id (fun () ->
    compute_rcs_ty seen ctx rc (Lazy.force q.q_body)
  )
and compute_rcs_ty seen ctx rc tv =
  let t = Context.read_var ctx Context.typ tv in
  let id = GT.typ_id t in
  addref_ty rc id;
  Seen.guard seen.GT.seen_ty id (fun () ->
    List.iter (GT.ty_q_kids t) ~f:(compute_rcs_q seen ctx rc)
  )

let compute_rcs_q ctx qv =
  let rc_ref = ref empty_rcs in
  compute_rcs_q (GT.empty_seen ()) ctx rc_ref qv;
  !rc_ref

(* Return the quant for the variable's b_target, or None if it
   is bound on a G-node *)
let maybe_q_target ctx bv =
  let {GT.b_target; _} = Context.read_var ctx Context.bound bv in
  match b_target with
  | `G _ -> None
  | `Q qv -> Some (Context.read_var ctx Context.quant qv).q_id


type bind_src =
    [ `Q of GT.quant GT.var
    | `Ty of GT.typ GT.var
    ]
type binding = (bind_src * GT.Ids.Quant.t)

(* enumerate_binidngs_* walk over the type graph, and (lazily)
   return a list of binding edges that target q-nodes. Each
   binding edge is a pair (node, target), where target is the
   GT.quant on which node is bound, and node is
   [ `Q quant var | `Ty typ var ]. *)
let rec enumerate_bindings_q seen ctx qv =
  let q = Context.read_var ctx Context.quant qv in
  Seen.get seen.GT.seen_q q.q_id (fun () ->
    let body = enumerate_bindings_ty seen ctx (Lazy.force q.q_body) in
    match maybe_q_target ctx q.q_bound with
    | None -> body
    | Some q' -> lazy ((`Q qv, q') :: Lazy.force body)
  )
and enumerate_bindings_ty seen ctx tv =
  let typ = Context.read_var ctx Context.typ tv in
  Seen.get seen.GT.seen_ty (GT.typ_id typ) (fun () ->
    let kids = lazy (
      GT.ty_q_kids typ
        |> List.map ~f:(fun q ->
            Lazy.force (enumerate_bindings_q seen ctx q)
          )
        |> List.concat
      )
    in
    match typ with
    | `Free {tv_bound; _} ->
        begin match maybe_q_target ctx tv_bound with
        | None -> kids
        | Some q -> lazy ((`Ty tv, q) :: Lazy.force kids)
        end
    | _ -> kids
  )

(* Turn the list of bindings returned by enumerate_bindings_* into a map
   from q -> nodes bound on q. *)
let accumulate_bindings : binding list -> bind_src list GT.Ids.QuantMap.t =
  fun binds ->
    List.fold
      binds
      ~init:(Map.empty (module GT.Ids.Quant))
      ~f:(fun m (child, q_id) ->
        Map.update m q_id ~f:(fun v ->
          child :: Option.value v ~default:[]
        )
      )

(* State & info bundle needed to display a type. *)
type display_ctx = {
  ctx: Context.t; (* General type context, for reading variables *)

  (* These are computed up front, and never change: *)
  rc: rc; (* Refcounts for each node *)
  bindings: bind_src list GT.Ids.QuantMap.t; (* Map from each q node to nodes bound on it. *)

  (* For q-nodes we have determined are recursive types, this contains
     variable names to use for those types. *)
  recursive_vars: Var.t GT.Ids.QuantMap.t ref;

  (* List of q-nodes that are structural parents of the node we are currently
     examining. Used to catch recursive types. *)
  parents: GT.Ids.QuantSet.t;

  (* The variance of our position in the type. *)
  sign: Sign.t;

  (* memoized results for each node. *)
  memo_types: (unit DT.t, unit DT.t) GT.seen;
}

(* Generate the initial display context for printing the node. *)
let build_display_ctx : Context.t -> GT.quant GT.var -> display_ctx =
  fun ctx qv -> {
      rc = compute_rcs_q ctx qv;
      bindings =
        enumerate_bindings_q (GT.empty_seen ()) ctx qv
        |> Lazy.force
        |> accumulate_bindings;
      ctx;
      recursive_vars = ref (Map.empty (module GT.Ids.Quant));
      parents = Set.empty (module GT.Ids.Quant);
      sign = `Pos;
      memo_types = GT.empty_seen ();
    }

(* Mark the node as recursive if it isn't already, and return the
   variable name to use for it. *)
let as_recursive_var : display_ctx -> GT.Ids.Quant.t -> Var.t =
  fun dc qid -> match Map.find !(dc.recursive_vars) qid with
    | Some v -> v
    | None ->
        begin
          let v = Gensym.anon_var (Context.get_ctr dc.ctx) in
          dc.recursive_vars := Map.set ~key:qid ~data:v !(dc.recursive_vars);
          v
        end
(* If the node is known to be a recursive type, wrap the type it in a rec.
   binder, with the appropriate variable name. Otherwise just return it as-is. *)
let maybe_with_recursive : display_ctx -> GT.Ids.Quant.t -> unit DT.t -> unit DT.t =
  fun dc qid body -> match Map.find !(dc.recursive_vars) qid with
    | None -> body
    | Some v -> DT.Recur {
        mu_info = ();
        mu_var = v;
        mu_body = body;
      }

(*
let degraph_quant ctx qv =
  let rc = {
    rc_q = ref (Map.empty (module GT.Ids.Quant));
    rc_ty = ref (Map.empty (module GT.Ids.Type));
  }
  in
  compute_rcs_q (GT.empty_seen ()) ctx rc qv;
  let binds = accumulate_bindings (Lazy.force (enumerate_bindings_q (GT.empty_seen ()) ctx qv)) in

  let recursive = ref (Set.empty (module GT.Ids.Quant)) in
  let q_names = ref (Map.empty (module GT.Ids.Quant)) in
  let ty_names = ref (Map.empty (module GT.Ids.Type)) in

  let make_var mapref id =
    let v = Gensym.anon_var (Context.get_ctr ctx) in
    recursive := Map.set ~key:id ~data:v !mapref;
    v
  in

  let rec go_q qv ~parents =
    let q = Context.read_var ctx Context.quant qv in
    if Set.mem parents q.q_id then
      begin
        let v = make_var q_names q.q_id in
        recursive := Map.set ~key:q.q_id ~data:v !recursive;
        DT.Var {
          v_var = v;
          v_info = ();
          v_src = `Generated;
        }
      end
    else
      let body = go_ty (Lazy.force q.q_body) ~parents:(Set.add parents q.q_id) in
      let pre_quant =
        if Set.mem !recursive q.q_id then
          DT.Recur {
              mu_info = ();
              mu_var = Map.find_exn !q_names q.q_id;
              mu_body = body;
            }
        else
          body
      in
      let with_quant =
      if (Map.find_exn !(rc.rc_q) q.q_id) > 1 then
          begin
            let v = make_var q_names q.q_id in

          end
        else
          (* TODO: bind quantifiers. *)
          body
      end
  and go_ty tv ~parents =
    let t = Context.read_var ctx Context.typ tv in
    match t with
    | `Free _ -> failwith "TODO"
    | `Ctor(_, c) -> go_ctor ~parents c
    | `Lambda(_, p, r) -> go_lambda ~parents p r
    | `Apply(_, f, arg) -> go_apply ~parents f arg
    | `Poison _ -> failwith "TODO"
  and go_ctor ~parents = function
    | _ -> failwith "TODO"
  and go_lambda ~parents _p _r =
    failwith "TODO"
  and go_apply ~parents fn arg =
    DT.App {
      app_info = ();
      app_fn = go_q ~parents fn;
      app_arg = go_q ~parents arg;
    }
  in
  go_q ~parents:(Set.empty (module GT.Ids.Quant)) qv
   *)


(* TODO:
   - walk over the graph, and generate nodes in a bottom-up fashion.
   - Keep track of parent nodes on the way down; if you see a node
     you've seen before, emit a type variable and add it to the list
     of recursive nodes. On the way back up, if a node is in the
     recursive set, add a rec binder to it with the appropriate variable
     name.
   - At each q node, for each of the nodes bound on it with rc > 1, and
     for each bottom node with rc == 1, emit a quantifier, with that node
     as its bound. Choice of exists or all quantifier depends on the binder
     flag and whether the quant appears in positive or negative position.
*)
