

let fix : ('a Lazy.t -> 'b) -> ('b Lazy.t -> 'a) -> ('b * 'a) =
  fun f g ->
  let rec a = lazy (g b)
  and b = lazy (f a)
  in (Lazy.force b, Lazy.force a)

module IO = struct
  let slurp_file (path : string) : string Lwt.t =
    Lwt_io.with_file ~mode:Lwt_io.Input path Lwt_io.read
end

let find_exn: ('k, 'v, 'cmp) Map.t -> 'k -> 'v =
  fun map k ->
  match Map.find map k with
  | Some v -> v
  | None -> MuleErr.bug "find_exn: not found"
