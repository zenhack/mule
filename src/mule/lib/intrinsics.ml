open Common_ast

module C = Const
module D = Desugared_ast
module R = Runtime_ast
module S = Surface_ast

open Typecheck_types

let int_t = D.Type.Named{n_info = ktype; n_name = `Int}
let text_t = D.Type.Named{n_info = ktype; n_name = `Text}
let fn_t p r = D.Type.Fn {
    fn_info = ktype;
    fn_pvar = None;
    fn_param = p;
    fn_ret = r;
  }
let char_t = D.Type.Named{n_info = ktype; n_name = `Char}

let int_binop_t =
  fn_t int_t (fn_t int_t int_t)
let int_binop_v f =
  R.prim (fun x -> R.prim (fun y -> R.int (f (R.assert_int x) (R.assert_int y))))

let dict kvs =
  List.map kvs ~f:(fun (k, v) -> (Var.of_string k, v))
  |> Map.of_alist_exn (module Var)

let row kvs = D.Type.{
    row_info = krow;
    row_fields = List.map kvs ~f:(fun (k, v) -> (Label.of_string k, v));
    row_rest = None;
  }

let recordType tys vals =
  D.Type.Record {
    r_src = None;
    r_info = ktype;
    r_types = row tys;
    r_values = row vals;
  }

let recordVal = R.mk_record

let unionType r = D.Type.Union { u_row = row r }

let unionVal c v = R.Expr.Ctor(Label.of_string c, v)

let maybe t = unionType [ "Some", t; "None", (recordType [] []) ]

let values = dict [
    "int",
    ( recordType [ "t", int_t ] [
          "add", int_binop_t;
          "sub", int_binop_t;
          "mul", int_binop_t;
          "div", int_binop_t;
          "rem", int_binop_t;
        ]
    , recordVal [
          "add", int_binop_v Z.add;
          "sub", int_binop_v Z.sub;
          "mul", int_binop_v Z.mul;
          "div", int_binop_v Z.div;
          "rem", int_binop_v Z.rem;
        ]
    );
    "text",
    ( recordType [ "t", text_t ] [
          "append", fn_t text_t (fn_t text_t text_t);
          "from-int", fn_t int_t text_t;
          "length", fn_t text_t int_t;
          "uncons", fn_t text_t (maybe (recordType [] ["head", char_t; "tail", text_t]));
        ]
    , recordVal [
          "append", R.prim (fun l -> R.prim (fun r -> R.text (R.assert_text l ^ R.assert_text r)));
          "from-int",
          R.prim (fun x -> R.text (Z.to_string (R.assert_int x)));
          "length",
          R.prim (fun s -> R.int (Z.of_int (String.length (R.assert_text s))));
          "uncons",
          R.prim (fun s ->
            match R.assert_text s with
            | "" -> unionVal "None" (recordVal [])
            | txt -> unionVal "Some"
                  (recordVal [
                        "head", R.char (txt.[0]);
                        "tail", R.text (String.drop_prefix txt 1);
                      ]
                  )
          )
        ]
    );
    "char",
    ( recordType [ "t", char_t ] []
    , recordVal []
    );
  ]

let types = dict [
    "int", int_t;
    "text", text_t;
    "char", char_t;
  ]