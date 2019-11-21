
open Common_ast
module R = Runtime_ast
module C = Const

let type_of_string_exn s =
  match MParser.parse_string Parser.typ s "<builtin>" with
  | MParser.Failed (msg, _) -> failwith ("parse failed : " ^ msg)
  | MParser.Success ty -> Desugar.desugar_type ty

type runner = {
  want_type : Desugared_ast_kind.maybe_kind Desugared_ast_type.t;
  run : R.Expr.t -> R.Expr.t Lwt.t;
}

let ignore_io io =
  R.prim_io (fun () -> Lwt.map (fun _ -> R.Expr.Record (Map.empty (module Label))) (io ()))

let io_just = R.prim (fun x ->
    R.prim_io (fun () -> Lwt.return x)
  )

let io_then = R.prim (fun x -> R.prim (fun f -> R.prim_io (fun () ->
    let%lwt x' = R.assert_io x () in
    R.assert_io (Eval.eval(App(f, x'))) ()
  )))

let io_print =
  R.prim (fun s -> ignore_io (fun () -> Lwt_io.write Lwt_io.stdout (R.assert_text s)))

let io_get_line = R.prim_io (fun () ->
    Lwt_io.read_line Lwt_io.stdin
    |> Lwt.map R.text
  )

let root_io_val =
  R.mk_record [
    "just", io_just;
    "then", io_then;
    "print", io_print;
    "get-line", io_get_line;
  ]

let root_io = {
  want_type = type_of_string_exn
      "(io : {
        , type cmd a
        , just : all a. a -> cmd a
        , then : all a b. cmd a -> (a -> cmd b) -> cmd b
        , print : text -> cmd {}
        , get-line : cmd text
      }
    )
    ->
    io.cmd {}
    ";
  run = fun f -> R.assert_io (Eval.eval (R.Expr.App (f, root_io_val))) ();
}

let by_name =
  Map.of_alist_exn (module String) [
    "root-io", root_io;
  ]
