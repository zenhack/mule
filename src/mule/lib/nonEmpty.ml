
type 'a t = ('a * 'a list)

let cons a (b, cs) = (a, b::cs)
let singleton x = (x, [])
let rev (x, xs) =
  match List.rev (x::xs) with
  | (y::ys) -> (y, ys)
  | [] -> failwith "Impossible"
