let () =
  match Array.length Sys.argv with
  | 1 -> Repl.loop ()
  | len ->
      for i = 1 to len - 1 do
        let path = Array.get Sys.argv i in
        let fd = In.create path in
        let str = In.input_all fd in
        In.close fd;
        match Run.run str with
          | Ok () -> ()
          | Error () -> Caml.exit 1
      done
