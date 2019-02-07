let () =
  match Array.length Sys.argv with
  | 1 -> Repl.loop ()
  | len ->
      for i = 1 to len do
        let path = Array.get Sys.argv i in
        (* TODO: actually process the files. *)
        print_endline path
      done
