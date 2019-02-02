
let rec loop () =
  print_string "#ready> ";
  let line = try read_line () with
    End_of_file ->
      (* Make sure the terminal prompt shows up on a new line: *)
      print_endline "";
      exit 0
  in
  match MParser.parse_string Parser.repl_line line () with
  | MParser.Failed (msg, _) ->
      print_endline "Parse Error:";
      print_endline msg;
      loop ()
  | MParser.Success None ->
      (* User entered a blank line *)
      loop ()
  | MParser.Success (Some expr) ->
      Eval.eval expr
        |> Pretty.expr
        |> print_endline;
      loop ()

let () = loop ()
