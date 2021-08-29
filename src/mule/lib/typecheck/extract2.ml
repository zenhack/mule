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

type rc = {
  rc_q: int GT.Ids.QuantMap.t ref;
  rc_ty: int GT.Ids.TypeMap.t ref;
}

let addref_q {rc_q; _} id =
  rc_q := Map.update !rc_q id ~f:(fun v -> Option.value v ~default:0 + 1)
let addref_ty {rc_ty; _} id =
  rc_ty := Map.update !rc_ty id ~f:(fun v -> Option.value v ~default:0 + 1)

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

(* Return the quant for the variable's b_target, or None if it
   is bound on a G-node *)
let maybe_q_target ctx bv =
  let {GT.b_target; _} = Context.read_var ctx Context.bound bv in
  match b_target with
  | `G _ -> None
  | `Q qv -> Some (Context.read_var ctx Context.quant qv).q_id


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
let accumulate_bindings binds =
  List.fold
    binds
    ~init:(Map.empty (module GT.Ids.Quant))
    ~f:(fun m (child, q) ->
      Map.update m q.GT.q_id ~f:(fun v ->
        child :: Option.value v ~default:[]
      )
    )

(* TODO:
   - Compute refcounts for each type.
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
