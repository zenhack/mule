
let rec loop : unit -> 'a = fun () ->
  ignore (Stdio.print_string "#mule> ");
  ignore (Stdio.Out_channel.flush Stdio.stdout);
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
  let%lwt _ = Run.run line in
  loop ()
