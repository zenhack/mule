(* Let_syntax module for lwt. *)

let return =
  Lwt.return

let both x y =
  Lwt.(
    x
    >>= fun x' -> y
    >>= fun y' -> return (x', y')
  )

let map x ~f =
  Lwt.map f x

let bind x ~f =
  Lwt.(x >>= f)
