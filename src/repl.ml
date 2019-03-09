let rec loop () =
  print_string "#mule> ";
  let line = try read_line () with
    End_of_file ->
      (* Make sure the terminal prompt shows up on a new line: *)
      print_endline "";
      exit 0
  in
  let _ = Run.run line in
  loop ()
