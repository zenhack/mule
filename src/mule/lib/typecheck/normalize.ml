module GT = Graph_types

let rec whnf_typ ctx t = match t with
  | `Free _ | `Ctor _ | `Lambda _ | `Poison _ -> t
  | `Apply (id, f, arg) ->
      begin
        Context.modify_var ctx Context.quant (whnf_q ctx) f;
        apply_qq ctx id f arg
      end
and whnf_q ctx q =
  Context.modify_var ctx Context.typ (whnf_typ ctx) (Lazy.force q.q_body);
  q
and apply_qq ctx app_id f arg =
  let ft = Lazy.force (Context.read_var ctx Context.quant f).q_body in
  match Context.read_var ctx Context.typ ft with
  | `Lambda (_id, _param, _body) ->
      failwith "TODO: apply_qq lambda"
  | _ ->
    `Apply (app_id, f, arg)
