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

let relabel_type () =
  (* We're careful about the order in which we walk the tree, so
   * variables are always left to right. *)
  let open Ast.Desugared.Type in
  let get = new_get () in
  let get v = Var.of_string (get v) in
  let rec go = function
    | App(i, f, x) ->
        let f' = go f in
        let x' = go x in
        App(i, f', x')
    | TypeLam(i, v, t) ->
        let v = get v in
        TypeLam(i, v, go t)
    | Opaque i -> Opaque i
    | Named(i, s) -> Named (i, s)
    | Fn (i, v, l, r) ->
        let v' = Option.map v ~f:get in
        let l' = go l in
        let r' = go r in
        Fn (i, v', l', r')
    | Recur (i, v, body) ->
        let v' = get v in
        let body' = go body in
        Recur (i, v', body')
    | Var (i, v) -> Var (i, get v)
    | Record {r_info; r_types; r_values} ->
        let r_types = go_row r_types in
        let r_values = go_row r_values in
        Record { r_info; r_types; r_values }
    | Union row -> Union (go_row row)
    | Quant (i, q, v, body) ->
        let v' = get v in
        let body' = go body in
        Quant (i, q, v', body')
    | Path(i, v, ls) -> Path(i, get v, ls)
  and go_row (i, fields, rest) =
    let fields' = List.map fields ~f:(fun (l, ty) -> (l, go ty)) in
    let rest' = Option.map rest ~f:get in
    (i, fields', rest')
  in
  go
