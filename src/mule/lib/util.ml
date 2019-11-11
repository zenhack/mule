let find_exn: ('k, 'v, 'cmp) Map.t -> 'k -> 'v =
  fun map k ->
  match Map.find map k with
  | Some v -> v
  | None -> MuleErr.bug "find_exn: not found"
