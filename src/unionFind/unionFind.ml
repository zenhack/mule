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
let rec get_rep_val: 'a var -> ('a var * 'a) =
  fun var -> match !var with
    | Repr value -> (var, value)
    | Ptr var' ->
        let (rep, value) = get_rep_val var' in
        var := Ptr rep;
        (rep, value)

let get var =
  snd (get_rep_val var)

let get_rep var =
  fst (get_rep_val var)

let equal l r =
  let (l', _), (r', _) = get_rep_val l, get_rep_val r in
  phys_equal l' r'

let merge f l r =
  let (lrep, lval), (rrep, rval) = (get_rep_val l, get_rep_val r) in
  if phys_equal lrep rrep then
    ()
  else begin
    let value = f lval rval in
    (* We need to fetch these again, in case they were modified by
     * [f]: *)
    let lrep, rrep = get_rep l, get_rep r in
    rrep := Ptr lrep;
    lrep := Repr value
  end

let set value var =
  let new_var = make value in
  merge (fun n _o -> n) new_var var

let modify f var =
  set (f (get var)) var
