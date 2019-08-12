
module R = Ast.Runtime
module C = Ast.Const

let type_of_string_exn s =
  match MParser.parse_string Parser.typ s () with
  | MParser.Failed (msg, _) -> failwith ("parse failed : " ^ msg)
  | MParser.Success ty -> ty

type runner =
  { want_type : Ast.Surface.Type.t
  ; run : R.Expr.t -> R.Expr.t Lwt.t
  }

(* TODO: some of these helpers are duplicated from intrinsics.ml;
 * factor them out. *)
let prim x =
  R.Expr.Prim x

let prim_io x =
  R.Expr.PrimIO x

let assert_io = function
  | R.Expr.PrimIO io -> io
  | _ -> failwith "BUG: run-time type error."

let assert_text = function
  | R.Expr.Const (C.Text s) -> s
  | _ -> failwith "BUG: run-time type error."

let ignore_io io =
  prim_io (fun () -> Lwt.map (fun _ -> R.Expr.Record LabelMap.empty) (io ()))

let io_just = prim (fun x ->
    prim_io (fun () -> Lwt.return x)
  )

let io_then = prim (fun x -> prim(fun f -> prim_io (fun () ->
    let%lwt x' = assert_io x () in
    assert_io (Eval.eval(App(f, x'))) ()
  )))

let io_print =
  prim (fun s -> ignore_io (fun () -> Lwt_io.write Lwt_io.stdout (assert_text s)))

let io_get_line = prim_io (fun () ->
  Lwt_io.read_line Lwt_io.stdin
  |> Lwt.map (fun s -> R.Expr.Const (C.Text s))
  )

let mk_record fields =
  fields
  |> List.map ~f:(fun (k, v) -> (Ast.Label.of_string k, v))
  |> Map.of_alist_exn (module Ast.Label)
  |> fun lblmap -> R.Expr.Record lblmap

let root_io_val =
  mk_record
    [ "just", io_just
    ; "then", io_then
    ; "print", io_print
    ; "get-line", io_get_line
    ]

let root_io =
  { want_type = type_of_string_exn
        "all iocmd. {
        , type cmd a = iocmd a
        , just : all a. a -> cmd a
        , then : all a b. cmd a -> (a -> cmd b) -> cmd b
        , print : text -> cmd {}
        , get-line : cmd text
      }
    ->
    iocmd {}
    "
  ; run = fun f -> assert_io (Eval.eval (R.Expr.App (f, root_io_val))) ()
  }


let by_name =
  [ "root-io", root_io
  ]
  |> Map.of_alist_exn (module String)
