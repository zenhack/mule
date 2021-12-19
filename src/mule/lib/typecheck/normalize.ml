module GT = Graph_types

(* Clone the interior of a subgraph rooted at qv, where the interior
   is defined as nodes bound at b_target or below. Nodes bound above
   b_target will be shared with the original. *)
let rec clone_q seen ctx qv ~is_root ~b_target =
  let q = Context.read_var ctx Context.quant qv in
  Seen.get seen.Expand_reduce.seen_q q.q_id (fun () ->
    let orig_bound = Context.read_var ctx Context.bound q.q_bound in
    if Expand_reduce.bound_under seen ctx ~limit:b_target ~target:orig_bound.b_target then
      let q_id = GT.Ids.Quant.fresh (Context.get_ctr ctx) in
      let q_body = clone_typ seen ctx (Lazy.force q.q_body) ~b_target in
      let q_bound =
        if is_root then
          Context.make_var ctx Context.bound {b_target; b_flag = `Flex}
        else
          clone_bound seen ctx q.q_bound ~b_target
      in
      Context.make_var ctx Context.quant {
        q_id;
        q_bound;
        q_merged = Set.singleton (module GT.Ids.Quant) q_id;
        q_body = lazy q_body;
      }
    else
      qv
  )
and clone_bound seen ctx bv ~b_target =
  let b = Context.read_var ctx Context.bound bv in
  match b.b_target with
  | `G _ ->
      (* TODO: restructure to avoid checking this at runtime. *)
      MuleErr.bug
        ( "Impossible: shouldn't have called this with a G; " ^
          "that would imply that this is bound above the apply node."
        )
  | `Q qv ->
      Context.make_var ctx Context.bound {
        b_target = `Q (clone_q seen ctx qv ~b_target ~is_root:false);
        b_flag = b.b_flag;
      }
(* Like clone_q, but for type nodes. *)
and clone_typ seen ctx tv ~b_target =
  let t = Context.read_var ctx Context.typ tv in
  Seen.get seen.Expand_reduce.seen_ty (GT.typ_id t) (fun () ->
    let clone_q' qv = clone_q seen ctx qv ~is_root:false ~b_target in
    let id' = GT.Ids.Type.fresh (Context.get_ctr ctx) in
    match t with
    | `Free ftv ->
        let bnd = Context.read_var ctx Context.bound ftv.tv_bound in
        if Expand_reduce.bound_under seen ctx ~limit:b_target ~target:bnd.b_target then
          Context.make_var ctx Context.typ (`Free {
            tv_id = id';
            tv_merged = Set.singleton (module GT.Ids.Type) id';
            tv_bound = clone_bound seen ctx ftv.tv_bound ~b_target;
            tv_kind = ftv.tv_kind;
          })
        else
          tv
    | _ ->
        Context.make_var ctx Context.typ (Expand_reduce.clone_map_typ ~new_id:id' ~f:clone_q' t)
  )

let get_qv_typ ctx qv =
  let q = Context.read_var ctx Context.quant qv in
  let body = Lazy.force q.q_body in
  Context.read_var ctx Context.typ body

let rec whnf_typ ctx qv t = match t with
  | `Free _ | `Ctor _ | `Lambda _ | `Poison _ -> t
  | `Apply (id, f, arg) ->
      begin
        Context.modify_var ctx Context.quant (whnf_q ctx qv) f;
        apply_qq ctx qv id f arg
      end
and whnf_q ctx qv q =
  Context.modify_var ctx Context.typ (whnf_typ ctx qv) (Lazy.force q.q_body);
  q
and apply_qq ctx qv app_id fq arg =
  match get_qv_typ ctx fq with
  | `Lambda (_, param, body) ->
    let (param, body) =
      let seen = Expand_reduce.make_seen () in
      let f = Context.read_var ctx Context.quant fq in
      let f_bnd = Context.read_var ctx Context.bound f.q_bound in
      if Expand_reduce.bound_under seen ctx ~limit:(`Q qv) ~target:f_bnd.b_target then
        (* Already localized to this `Apply; no need to copy, as there are
           no other uses. *)
        (param, body)
      else
        begin
          let fq' = clone_q seen ctx fq ~b_target:(`Q qv) ~is_root:true in
          match get_qv_typ ctx fq' with
          | `Lambda (_, param, body) -> (param, body)
          | _ -> MuleErr.bug "clone_q didn't return a lambda."
        end
    in
    let arg' = Context.read_var ctx Context.quant arg in
    let body' = Context.read_var ctx Context.quant body in
    Context.merge ctx Context.quant param arg arg';
    Context.merge ctx Context.quant qv body body';
    (* TODO/FIXME: set the bound on body to something legal and useful. *)
    Context.read_var ctx Context.typ (Lazy.force body'.q_body)
  | _ ->
    `Apply (app_id, fq, arg)

let whnf_qv ctx qv =
  Context.modify_var ctx Context.quant (whnf_q ctx qv) qv
