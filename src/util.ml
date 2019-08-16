

let fix : ('a Lazy.t -> 'b) -> ('b Lazy.t -> 'a) -> ('b * 'a) =
  fun f g ->
  let rec a = lazy (g b)
  and b = lazy (f a)
  in (Lazy.force b, Lazy.force a)

module IO = struct
  let slurp_file (path : string) : string Lwt.t =
    Lwt_io.with_file ~mode:Lwt_io.Input path Lwt_io.read
end
