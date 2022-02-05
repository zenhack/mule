
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

module Tests = struct
  let%test_unit _ =
    (* It should be okay to walk cycles with guard: *)
    let seen = make (module Int) in
    let values = ref [] in
    let rec go i =
      guard seen i (fun () ->
        values := i :: !values;
        go ((i + 1) % 10)
      )
    in
    go 0;
    let ok =
      Poly.equal
        !values
        [9;8;7;6;5;4;3;2;1;0]
    in
    if not ok then
      failwith (String.concat [
          "Incorrect result: ";
          "[ ";
          String.concat ~sep:";" (List.map ~f:Int.to_string !values);
          " ]";
        ])
end
