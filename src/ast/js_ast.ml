open Common_ast

module Expr = struct
  type t =
    | Var of Var.t
    | App of (t * t list) (* f(x,y,z...) *)
    | Object of (string * t) list (* {x: 0, y: 1, ...} *)
    | GetProp of (t * t) (* x[y] *)
    | String of string (* 'string literal' *)
    | Func of (Var.t * t) (* (x => y) *)
    | Ternary of (t * t * t) (* x ? y : z *)
    | Eq3 of (t * t) (* === *)
    | Undefined (* undefined *)

  let fmt emit =
    let rec go = function
      | Var v ->
          emit (Var.to_string v);
          (* In case v is a javascript keyword: *)
          emit "$"
      | App (f, args) ->
          go f;
          emit "(";
          List.iter
            (fun a -> go a; emit ",")
            args;
          emit ")"
      | Object fields ->
          (* We need to wrap objects in an extra set of parens, because for
           * some crazy reason, (x => {'x': ...}) isn't legal javascript.
           *)
          emit "({";
          List.iter
            (fun (k, v) -> go (String k); emit ":"; go v; emit ",")
            fields;
          emit "})"
      | GetProp(obj, prop) ->
          emit "("; go obj; emit ")["; go prop; emit "]"
      | String s ->
          (* FIXME: do proper escaping etc. Right now this works
           * OK since we don't have strings, so we only ever pass
           * labels, but at some point this will be very broken: *)
          emit "'"; emit s; emit "'"
      | Func (var, body) ->
          emit "("; emit (Var.to_string var); emit "$=>"; go body; emit ")"
      | Ternary (cond, t, f) ->
          emit "("; go cond; emit ")?("; go t; emit "):("; go f; emit ")"
      | Eq3 (l, r) ->
          emit "("; go l; emit ")===("; go r; emit ")"
      | Undefined ->
          emit "undefined"
    in go
end
