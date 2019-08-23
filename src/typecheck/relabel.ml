open Ast

let letters =
  Char.all
  |> List.filter ~f:Char.is_lowercase
  |> List.map ~f:(String.make 1)
  |> Sequence.of_list

let nats =
  let open Sequence.Generator in
  let rec go n =
    let t = "t" ^ Int.to_string n in
    yield t >>= fun () -> go (n + 1)
  in
  run (go 0)

let typevars =
  Sequence.append letters nats

let new_get () =
  let seq = ref typevars in
  let seq_next () =
    match Sequence.next !seq with
    | None -> failwith "impossible" (* the seq is infinite. *)
    | Some (x, xs) ->
        seq := xs;
        x
  in
  Memoize.memoize (fun _ -> seq_next ())

let relabel_type: unit -> 'a Desugared.Type.t -> 'a Desugared.Type.t = fun () ->
  (* We're careful about the order in which we walk the tree, so
   * variables are always left to right. *)
  let open Desugared.Type in
  let get = new_get () in
  let get v = Var.of_string (get v) in
  let rec go typ = match typ with
    | App{app_info; app_fn = f; app_arg = x} ->
        let f' = go f in
        let x' = go x in
        App{app_info; app_fn = f'; app_arg = x'}
    | TypeLam{tl_info; tl_param = v; tl_body = t} ->
        let v = get v in
        TypeLam{tl_info; tl_param = v; tl_body = go t}
    | Opaque _ | Named _ -> typ
    | Fn {fn_info; fn_pvar = v; fn_param = l; fn_ret = r} ->
        let v' = Option.map v ~f:get in
        let l' = go l in
        let r' = go r in
        Fn {fn_info; fn_pvar = v'; fn_param = l'; fn_ret = r'}
    | Recur {mu_info; mu_var; mu_body} ->
        let v' = get mu_var in
        let body' = go mu_body in
        Recur {mu_info; mu_var = v'; mu_body = body'}
    | Var {v_info; v_var} -> Var{v_info; v_var = get v_var}
    | Record {r_info; r_types; r_values; r_src} ->
        let r_types = go_row r_types in
        let r_values = go_row r_values in
        Record { r_src; r_info; r_types; r_values }
    | Union {u_row} -> Union {u_row = go_row u_row}
    | Quant {q_info; q_quant; q_var = v; q_body} ->
        let v' = get v in
        let body' = go q_body in
        Quant {q_info; q_quant; q_var = v'; q_body = body'}
    | Path{p_info; p_var; p_lbls} -> Path {
        p_info;
        p_var = get p_var;
        p_lbls;
      }
  and go_row (i, fields, rest) =
    let fields' = List.map fields ~f:(fun (l, ty) -> (l, go ty)) in
    let rest' = Option.map rest ~f:get in
    (i, fields', rest')
  in
  go
