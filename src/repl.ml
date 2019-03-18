
let rec loop () =
  Out.output_string Stdio.stdout "#mule> ";
  match In.input_line Stdio.stdin with
  | Some line ->
      let _ = Run.run line in
      loop ()
  | None ->
      (* Make sure the terminal prompt shows up on a new line: *)
      Stdio.print_endline "";
      Caml.exit 0
