(* This module is responsible for turning a graphical type
   into a syntactic one.

   We borrow and extend a trick from {Leijen 2005}: the authors observe
   that type variables that are used only once, and are either flexible
   in positive position or rigid in negative position can be inlined,
   reducing the need to use the bounded-quantification syntax.

   The extension is that, since mule also has existential quantifiers,
   we can use those for rigid variables in positive position or flexible
   variables in negative position -- so the bounded quantification syntax
   is only necessary when the type is truly inexpressible as a tree.

   Much of the logic in this module has to do with preparation; e.g.
   we first compute reference counts for each type, so we can easily
   tell whether we should inline a type.
*)

module GT = Graph_types

type seen = {
  seen_q: (GT.Ids.Quant.t, unit) Seen.t;
  seen_ty: (GT.Ids.Type.t, unit) Seen.t;
}

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
  Seen.guard seen.seen_q q.q_id (fun () ->
    compute_rcs_ty seen ctx rc (Lazy.force q.q_body)
  )
and compute_rcs_ty seen ctx rc tv =
  let t = Context.read_var ctx Context.typ tv in
  let id = GT.typ_id t in
  addref_ty rc id;
  Seen.guard seen.seen_ty id (fun () ->
    match t with
    | `Ctor (_, `Type (`Fn (q_param, q_result))) ->
        compute_rcs_q seen ctx rc q_param;
        compute_rcs_q seen ctx rc q_result
    | `Ctor (_, `Type (`Record (q_types, q_values))) ->
        compute_rcs_q seen ctx rc q_types;
        compute_rcs_q seen ctx rc q_values
    | `Ctor (_, `Type (`Union q_variants)) ->
        compute_rcs_q seen ctx rc q_variants
    | `Ctor (_, `Row (`Extend (_, q_head, q_tail))) ->
        compute_rcs_q seen ctx rc q_head;
        compute_rcs_q seen ctx rc q_tail
    | `Lambda (_, q_param, q_body) ->
        compute_rcs_q seen ctx rc q_param;
        compute_rcs_q seen ctx rc q_body
    | `Apply (_, q_fn, q_arg) ->
        compute_rcs_q seen ctx rc q_fn;
        compute_rcs_q seen ctx rc q_arg
    | `Free _
    | `Ctor (_, `Type (`Const _))
    | `Ctor (_, `Row `Empty)
    | `Poison _ -> ()
  )
