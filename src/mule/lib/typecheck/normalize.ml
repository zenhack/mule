module GT = Graph_types

let clone_q _seen _ctx _b_target _q =
  failwith "TODO: clone_lambda"

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
          let fq' = clone_q seen ctx (`Q qv) fq in
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
