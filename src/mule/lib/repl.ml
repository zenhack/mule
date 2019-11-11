
let rec loop : unit -> 'a Lwt.t = fun () ->
  let%lwt _ = Lwt_io.write Lwt_io.stdout "#mule> " in
  let%lwt _ = Lwt_io.flush Lwt_io.stdout in
  let%lwt line =
    Lwt.catch
      (fun () -> Lwt_io.read_line Lwt_io.stdin)
      (function
        | End_of_file ->
            (* Make sure the terminal prompt shows up on a new line: *)
            let%lwt _ = Lwt_io.write Lwt_io.stdout "\n" in
            Caml.exit 0
        | e ->
            raise e
      )
  in
  let%lwt _ = Run.run line in
  loop ()
