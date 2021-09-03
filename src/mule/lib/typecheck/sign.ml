
type t = [ `Pos | `Neg ]

let flip = function
  | `Pos -> `Neg
  | `Neg -> `Pos

let mul x y =
  match x with
  | `Pos -> y
  | `Neg -> flip y
