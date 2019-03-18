open Base

module In_chan = Stdio.In_channel

let () =
  match Array.length Sys.argv with
  | 1 -> Repl.loop ()
  | len ->
      for i = 1 to len - 1 do
        let path = Array.get Sys.argv i in
        let fd = In_chan.create path in
        let str = In_chan.input_all fd in
        In_chan.close fd;
        match Run.run str with
          | Ok () -> ()
          | Err () -> Caml.exit 1
      done
