
type ('k, 'v) t = {
  get: 'k -> (unit -> 'v) -> 'v;
  guard: 'k -> (unit -> 'v) -> unit;
}

let get s = s.get
let guard s = s.guard

let make cmp =
  let map = ref (Map.empty cmp) in
  let get k f = match Map.find !map k with
      | Some v -> Lazy.force v
      | None ->
          let v = lazy (f ()) in
          map := Map.set !map ~key:k ~data:v;
          Lazy.force v
  in
  let guard k f =
    if not (Map.mem !map k) then
      ignore (get k f)
  in
  {get; guard}
