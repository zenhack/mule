open Ast

module D = Desugared
module R = Runtime

open Typecheck_types

let int_t = D.Type.Named((), "int")
let text_t = D.Type.Named((), "text")
let fn_t p r = D.Type.Fn ((), p, r)

let prim x = R.Expr.Prim x

let assert_int = function
  | R.Expr.Integer n -> n
  | _ -> failwith "BUG: run-time type error."

let int_binop f =
  ( fn_t int_t (fn_t int_t int_t)
  , prim (fun x -> prim (fun y -> R.Expr.Integer (f (assert_int x) (assert_int y))))
  )

let dict kvs =
  List.map kvs ~f:(fun (k, v) -> (Var.of_string k, v))
  |> Map.of_alist_exn (module Var)

let values = dict
  [ "add", int_binop Z.add
  ; "sub", int_binop Z.sub
  ; "mul", int_binop Z.mul
  ; "div", int_binop Z.div
  ; "rem", int_binop Z.rem
  ]

let types = dict
  [ "int", int_t
  ; "text", text_t
  ]

let kinds = dict
  [ "int", kvar_type
  ; "text", kvar_type
  ]
