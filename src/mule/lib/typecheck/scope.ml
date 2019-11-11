
type t = int list

let equal ls rs = match ls, rs with
  | [], [] -> true
  | (l :: _), (r :: _) when l = r -> true
  | _ -> false

let rec lca ls rs = match ls, rs with
  | (l::ls'), (r :: rs') ->
      if l < r then
        lca ls rs'
      else if l > r then
        lca ls' rs
      else
        ls
  | _ -> []

let sexp_of_t ls =
  List.sexp_of_t Int.sexp_of_t ls

let empty = []

let make_child s =
  Gensym.gensym () :: s
