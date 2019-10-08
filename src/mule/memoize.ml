
let memoize f =
  let tbl = Caml.Hashtbl.create 10 in
  fun x ->
    match Caml.Hashtbl.find_opt tbl x with
    | Some y -> y
    | None ->
        let y = f x in
        Caml.Hashtbl.add tbl x y;
        y
