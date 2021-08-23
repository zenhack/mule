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
