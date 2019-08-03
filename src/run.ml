
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
    fun x -> Lwt.map Result.return x

  let result: ('a, MuleErr.t) Result.t -> 'a t =
    Lwt.return
end

let desugar_typecheck expr =
  let _ = Lint.check expr in
  let dexp = Desugar.desugar expr in
  let%lwt _ = display "Desugared" (Pretty.expr dexp) in
  let ty = Typecheck.typecheck dexp in
  let%lwt _ = display "inferred type"  (Pretty.typ ty) in
  Lwt.return dexp

let run : string -> unit LwtResult.t = fun input ->
  (* We really ought to rename repl line, since it's actually what we want
   * regardless of whether we're at the repl: *)
  match MParser.parse_string Parser.repl_line input () with
  | MParser.Failed (msg, _) ->
      let%lwt _ = display "Parse Error" msg in
      Lwt.return (Ok ())
  | MParser.Success None ->
      (* empty input *)
      Lwt.return (Ok ())
  | MParser.Success (Some expr) ->
      begin
        try%lwt
          let%lwt dexp = desugar_typecheck expr in
          let rexp = To_runtime.translate dexp in
          let%lwt _ = display "Runtime term" (Pretty.runtime_expr rexp) in
          let ret = Eval.eval rexp in
          let%lwt _ = display "Evaluated" (Pretty.runtime_expr ret) in
          Lwt.return (Ok ())
        with
        | MuleErr.MuleExn e ->
            let%lwt _ = print_endline (MuleErr.show e) in
            Lwt.return (Error e)
      end
