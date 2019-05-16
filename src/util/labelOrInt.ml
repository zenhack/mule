module T = struct
  type t =
    | Label of Ast.Label.t
    | Int of int

  let compare l r = match (l, r) with
    | Label l', Label r' -> Ast.Label.compare l' r'
    | Int l', Int r' -> Int.compare l' r'
    | Label _, Int _ -> -1
    | Int _, Label _ -> 1
end
include T
include Comparator.Make(T)
