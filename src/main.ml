let () =
  match Array.length Sys.argv with
  | 1 -> Repl.loop ()
  | len ->
      for i = 1 to len - 1 do
        let path = Array.get Sys.argv i in
        let fd = open_in path in
        let str = really_input_string fd (in_channel_length fd) in
        close_in fd;
        match Run.run str with
          | Ok () -> ()
          | Err () -> exit 1
      done
