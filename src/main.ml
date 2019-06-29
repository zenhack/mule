let each_file ~f =
    for i = 2 to Array.length Sys.argv - 1 do
      let path = Array.get Sys.argv i in
      let fd = In.create path in
      let str = In.input_all fd in
      In.close fd;
      match f str with
      | Ok () -> ()
      | Error () -> Caml.exit 1
    done

let () =
  if Array.length Sys.argv <= 1 then
    Repl.loop ()
  else
    begin match Array.get Sys.argv 1 with
    | "repl" ->
        Repl.loop ()
    | "test" ->
        each_file ~f:Run.run
    | cmd ->
        Out.print_endline ("Invalid command: " ^ cmd);
        Caml.exit 1
    end
