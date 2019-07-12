
module Let_syntax = Lwt_syntax

let rec loop : unit -> 'a Lwt.t = fun () ->
  let%bind _ = Lwt_io.write Lwt_io.stdout "#mule> " in
  let%bind _ = Lwt_io.flush Lwt_io.stdout in
  let%bind line =
    Lwt.catch
      (fun () -> Lwt_io.read_line Lwt_io.stdin)
      (function
        | End_of_file ->
          (* Make sure the terminal prompt shows up on a new line: *)
          let%bind _ = Lwt_io.write Lwt_io.stdout "\n" in
          Caml.exit 0
        | e ->
          raise e
      )
  in
  let%bind _ = Run.run line in
  loop ()
