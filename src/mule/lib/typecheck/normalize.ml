(*
open Mlftype

let rec whnf_typ : typ -> typ = fun t -> match t with
  | `Free _ | `Ctor _ | `Lambda -> t
  | `Apply (f, arg) ->
      begin
        UnionFind.modify whnf_q f;
        apply_qq f arg
      end
and whnf_q : quant -> quant = fun q ->
  UnionFind.modify whnf_typ q.q_body;
  q
and apply_qq f arg =
  match (UnionFind.get f).q_body | UnionFind.get with
  | `Lambda (_param, _body) ->
      failwith "TODO"
  | _ ->
      `Apply (f, arg)
   *)
