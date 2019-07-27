
let print_endline s =
  Lwt_io.write Lwt_io.stdout (s ^ "\n")

let display label text =
  let text =
    String.split_lines text
    |> List.map ~f:(fun line -> "\t" ^ line)
    |> String.concat ~sep:"\n"
  in
  print_endline ("\n" ^ label ^ ":\n\n" ^ text)

module LwtResult = struct
  type 'a t = ('a, MuleErr.t) Result.t Lwt.t

  let return x =
    Lwt.return (Ok x)

  let bind x ~f =
    Lwt.bind x (function
        | Ok x' -> f x'
        | Error e -> Lwt.return (Error e)
      )

  let both x y =
    let (>>=) x f = bind x ~f in
    x
    >>= fun x' -> y
    >>= fun y' -> return (x', y')

  let map x ~f =
    Lwt.map (Result.map ~f) x

  let lwt: 'a Lwt.t -> 'a t =
    Lwt.map Result.return

  let result: ('a, MuleErr.t) Result.t -> 'a t =
    Lwt.return
end

let desugar_typecheck expr =
  let module L = LwtResult in
  let module Let_syntax = L in

  let%bind _ = L.result (Lint.check expr) in
  let%bind dexp = L.result (Desugar.desugar expr) in
  let%bind _ = L.lwt (display "Desugared" (Pretty.expr dexp)) in
  let%bind ty = L.result (Typecheck.typecheck dexp) in
  let%bind _ = L.lwt (display "inferred type"  (Pretty.typ ty)) in
  L.return dexp

let run : string -> unit LwtResult.t = fun input ->
  (* We really ought to rename repl line, since it's actually what we want
   * regardless of whether we're at the repl: *)
  let module Let_syntax = Lwt_syntax in
  match MParser.parse_string Parser.repl_line input () with
  | MParser.Failed (msg, _) ->
      let%map _ = display "Parse Error" msg in
      Ok ()
  | MParser.Success None ->
      (* empty input *)
      Lwt.return (Ok ())
  | MParser.Success (Some expr) ->
      begin match%bind desugar_typecheck expr with
        | Error e ->
            let%map _ = print_endline (MuleErr.show e) in
            Error e
        | Ok dexp ->
            let rexp = To_runtime.translate dexp in
            let%bind _ = display "Runtime term" (Pretty.runtime_expr rexp) in
            let ret = Eval.eval rexp in
            let%map _ = display "Evaluated" (Pretty.runtime_expr ret) in
            Ok ()
      end
