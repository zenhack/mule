

let fix : ('a Lazy.t -> 'b) -> ('b Lazy.t -> 'a) -> ('b * 'a) =
  fun f g ->
  let rec a = lazy (g b)
  and b = lazy (f a)
  in (Lazy.force b, Lazy.force a)
