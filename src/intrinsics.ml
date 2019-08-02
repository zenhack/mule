open Ast

module D = Desugared
module R = Runtime

open Typecheck_types

let int_t = D.Type.Named(kvar_type, "int")
let text_t = D.Type.Named(kvar_type, "text")
let fn_t p r = D.Type.Fn (kvar_type, p, r)

let prim x = R.Expr.Prim x

let assert_int = function
  | R.Expr.Integer n -> n
  | _ -> failwith "BUG: run-time type error."

let assert_text = function
  | R.Expr.Text s -> s
  | _ -> failwith "BUG: run-time type error."

let int_binop f =
  ( fn_t int_t (fn_t int_t int_t)
  , prim (fun x -> prim (fun y -> R.Expr.Integer (f (assert_int x) (assert_int y))))
  )

let dict kvs =
  List.map kvs ~f:(fun (k, v) -> (Var.of_string k, v))
  |> Map.of_alist_exn (module Var)

let row kvs =
  ( kvar_row
  , List.map kvs ~f:(fun (k, v) -> (Label.of_string k, v))
  , None
  )

let recordType tys vals =
  D.Type.Record
    { r_info = kvar_type
    ; r_types = row tys
    ; r_values = row vals
    }

let recordVal kvs =
  R.Expr.Record (
    List.map kvs ~f:(fun (k, v) -> (Label.of_string k, v))
    |> Map.of_alist_exn (module Label)
  )

let values = dict
    [ "add", int_binop Z.add
    ; "sub", int_binop Z.sub
    ; "mul", int_binop Z.mul
    ; "div", int_binop Z.div
    ; "rem", int_binop Z.rem
    ; "text",
      ( recordType
          [ "t", text_t ]
          [ "append", fn_t text_t (fn_t text_t text_t)
          ; "from-int", fn_t int_t text_t
          ; "length", fn_t text_t int_t
          ]
      , recordVal
          [ "append",
            prim (fun l ->
                prim (fun r ->
                    R.Expr.Text (assert_text l ^ assert_text r)))
          ; "from-int",
            prim (fun x -> R.Expr.Text (Z.to_string (assert_int x)))
          ; "length",
            prim (fun s -> R.Expr.Integer (Z.of_int (String.length (assert_text s))))
          ]
      )
    ]

let types = dict
    [ "int", int_t
    ; "text", text_t
    ]

let kinds = dict
    [ "int", kvar_type
    ; "text", kvar_type
    ]
