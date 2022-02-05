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

let subst ctx ~var_qv ~val_qv =
  let qv_tv qv = Lazy.force (Context.read_var ctx Context.quant qv).q_body in
  let val_tv = qv_tv val_qv in
  let t = Context.read_var ctx Context.typ val_tv in
  let q = Context.read_var ctx Context.quant val_qv in
  Context.merge ctx Context.typ (qv_tv var_qv) val_tv t;
  Context.merge ctx Context.quant var_qv val_qv q

let clone_lambda ctx ~appq ~fq ~param ~body =
  let seen = Expand_reduce.make_seen () in
  let f = Context.read_var ctx Context.quant fq in
  let f_bnd = Context.read_var ctx Context.bound f.q_bound in
  if Expand_reduce.bound_under seen ctx ~limit:(`Q appq) ~target:f_bnd.b_target then
    (* Already localized to this `Apply; no need to copy, as there are
       no other uses. *)
    (param, body)
  else
    begin
      let fq' = clone_q seen ctx fq ~b_target:(`Q appq) ~is_root:true in
      match get_qv_typ ctx fq' with
      | `Lambda (_, param, body) -> (param, body)
      | _ -> MuleErr.bug "clone_q didn't return a lambda."
    end

let rec whnf_typ ctx qv t = match t with
  | `Free _ | `Ctor _ | `Lambda _
  | `GetField _ | `Fix _ | `Poison _ -> t

  | `Apply (id, f, arg) ->
      begin
        Context.modify_var ctx Context.quant (whnf_q ctx qv) f;
        apply_qq ctx qv id f arg
      end
and whnf_q ctx qv q =
  Context.modify_var ctx Context.typ (whnf_typ ctx qv) (Lazy.force q.q_body);
  q
and apply_qq ctx appq app_id fq arg =
  match get_qv_typ ctx fq with
  | `Lambda (_, param, body) ->
    let (param, body) = clone_lambda ctx ~appq ~fq ~param ~body in
    apply_lambda ctx ~appq ~param ~body ~arg
  | `GetField (_, section, lbl) ->
    Context.modify_var ctx Context.quant (whnf_q ctx appq) arg;
    begin match get_qv_typ ctx arg with
      | `Ctor(_, `Type(`Record(ts, vs))) ->
          let row = match section with
            | `Types -> ts
            | `Values -> vs
          in
          project_field ctx lbl row
      | _ ->
          `Apply (app_id, fq, arg)
    end
  | `Fix _ ->
    Context.modify_var ctx Context.quant (whnf_q ctx appq) arg;
    begin match get_qv_typ ctx arg with
      | `Lambda(_, param, body) ->
          let (param, body) = clone_lambda ctx ~appq ~fq:arg ~param ~body in
          apply_lambda ctx ~appq ~param ~body ~arg:body
      | _ ->
          `Apply (app_id, fq, arg)
    end

  | _ ->
    `Apply (app_id, fq, arg)
and project_field _ctx _lbl _row = failwith "TODO"
and apply_lambda ctx ~appq ~param ~body ~arg =
  (*
     1. Replace the parameter node with the argument.
     2. Set the body's bound to what the application's was.
     3. Replace the application with the body (whose parameter
        has now been substituted).

     1 and 3 have the effect of removing the explicit bounds.
  *)
  subst ctx ~var_qv:param ~val_qv:arg;
  let body' = Context.read_var ctx Context.quant body in
  let app_bnd = (Context.read_var ctx Context.quant appq).q_bound in
  Context.merge ctx Context.quant appq body { body' with q_bound = app_bnd };
  whnf_qv ctx appq;
  Context.read_var ctx Context.typ (Lazy.force body'.q_body)
and whnf_qv ctx qv =
  Context.modify_var ctx Context.quant (whnf_q ctx qv) qv
