module GT = Graph_types

let clone_lambda _qv (_id, _param, _body) =
  failwith "TODO: clone_lambda"

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
and apply_qq ctx qv app_id f arg =
  let ft = Lazy.force (Context.read_var ctx Context.quant f).q_body in
  match Context.read_var ctx Context.typ ft with
  | `Lambda lam ->
    (* TODO(perf): skip clone_lambda if the lambda is bound low enough. *)
    let (param, body) = clone_lambda qv lam in
    let arg' = Context.read_var ctx Context.quant arg in
    let body' = Context.read_var ctx Context.quant body in
    Context.merge ctx Context.quant param arg arg';
    Context.merge ctx Context.quant qv body body';
    Context.read_var ctx Context.typ (Lazy.force body'.q_body)
  | _ ->
    `Apply (app_id, f, arg)

let whnf_qv ctx qv =
  Context.modify_var ctx Context.quant (whnf_q ctx qv) qv
