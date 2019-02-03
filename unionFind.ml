
open OrErr

type 'a var =
  'a var_state ref
and 'a var_state =
  (* The representative; stores the value: *)
  | Repr of 'a
  (* Not the representative; points to another set: *)
  | Ptr of 'a var

let make v = ref (Repr v)

(* Get a pair [(rep, value)], where [rep] is the representative for the set,
 * and [value] is the associated value.
 *
 * performs path compression.
 *)
let rec get_rep_val var = match !var with
  | Repr value -> (var, value)
  | Ptr var' ->
      let (rep, value) = get_rep_val var' in
      var := Ptr rep;
      (rep, value)

let get var =
  let (_, value) = get_rep_val var in
  value

let merge f l r =
  let (lrep, lval), (rrep, rval) = (get_rep_val l, get_rep_val r) in
  if lrep == rrep then
    Ok lrep
  else begin match f lval rval with
  | Ok value ->
      lrep := Repr value;
      rrep := Ptr lrep;
      Ok rrep
  | Err e ->
      Err e
  end
