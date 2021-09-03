
type t = [ `Pos | `Neg ]

let flip = function
  | `Pos -> `Neg
  | `Neg -> `Pos

let mul x y =
  match x with
  | `Pos -> y
  | `Neg -> flip y

let quantifier_for sign flag =
  match sign, flag with
  | `Pos, `Flex
  | `Neg, `Rigid -> `All
  | `Pos, `Rigid
  | `Neg, `Flex -> `Exist
