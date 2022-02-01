
type 'a t = ('a * 'a list)

let cons a (b, cs) = (a, b::cs)
let singleton x = (x, [])
let map ~f (x, xs) =
  (f x, List.map ~f xs)
let rev (x, xs) =
  match List.rev (x::xs) with
  | (y::ys) -> (y, ys)
  | [] -> failwith "Impossible"
let to_list (x, xs) =
  x :: xs

let sexp_of_t of_elem lst =
  List.sexp_of_t of_elem (to_list lst)
