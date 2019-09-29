type t = Buffer.t -> unit

let to_string f =
  let buf = Buffer.create 0 in
  f buf;
  Buffer.contents buf

let s x buf = Buffer.add_string buf x
let c x buf = Buffer.add_char buf x
let concat ts buf = List.iter ts ~f:(fun add -> add buf)

let (^) f g buf =
  f buf;
  g buf

let empty _ = ()

let between l r x = l ^ x ^ r

let parens   = between (c '(') (c ')')
let brackets = between (c '[') (c ']')
let braces   = between (c '{') (c '}')

let sep_by sep = function
  | [] -> empty
  | (x :: xs) -> concat (x :: List.map xs ~f:(fun t -> sep ^ t))

let end_by term xs =
  List.map xs ~f:(fun x -> x ^ term)
  |> concat

let comma_sep = sep_by (c ',')
