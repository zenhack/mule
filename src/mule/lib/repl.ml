
let rec loop : unit -> 'a = fun () ->
  Stdio.print_string "#mule> ";
  Stdio.Out_channel.flush Stdio.stdout;
  let line =
    try
      Caml.read_line ()
    with
      | End_of_file ->
          (* Make sure the terminal prompt shows up on a new line: *)
          ignore (Stdio.print_endline "");
          Caml.exit 0
      | e ->
          raise e
  in
  Run.run line;
  loop ()
