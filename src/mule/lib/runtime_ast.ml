open Common_ast

module Expr = struct
  type 'a io = unit -> 'a Lwt.t

  let sexp_of_io _ _ = sexp_of_string "<io>"

  type t =
    | Var of int
    | Lam of (int * t list * t)
    | LetRec of ((int * t) list * t)
    | App of (t * t)
    | Record of t LabelMap.t
    | GetField of Label.t
    | Update of {
        old: t;
        label: Label.t;
        field: t;
      }
    | Ctor of (Label.t * t)
    | Match of branch
    | Lazy of (lazy_state ref) Lazy.t
    | Const of Const.t
    | Prim of (t -> t)
    | PrimIO of (t io)
  and branch =
    | BLabel of {
        lm_cases: branch LabelMap.t;
        lm_default: t option;
      }
    | BConst of {
        cm_cases: t ConstMap.t;
        cm_default: t option;
      }
    | BLeaf of t
  [@@deriving sexp_of]
  and lazy_state =
    | Delayed of (t list * t)
    | InProgress
    | Ready of t

  let rec pretty_t prec = function
    | Var _ | LetRec _ | App _ | GetField _ | Update _ | Match _ ->
        PP.string "<non-value>"
    | Lam _ -> PP.string "<lambda>"
    | Lazy _ -> PP.string "<lazy>"
    | Prim _ -> PP.string "<primitive-function>"
    | PrimIO _ -> PP.string "<primitive-io>"
    | Const c -> PP.string (Const.to_string c)
    | Ctor(lbl, arg) ->
        PP.(Prec.(parens_if_tighter_than prec AppFn (
            Label.pretty lbl ^/^ pretty_t AppArg arg
          )))
    | Record fields ->
        Map.to_alist fields
        |> List.map ~f:(fun (k, v) ->
          PP.(Label.pretty k ^/^ PP.string "=" ^/^ pretty_t Prec.TopLevel v)
        )
        |> PP.(opt_fst comma)
        |> PP.braces

  (* Convert a runtime value to a human readable string.
   *
   * This is intended for displaying *fully evaluated* values to the user. As such,
   * we punt on useful displaying of non-value expressions. Functions are opaque,
   * because:
   *
   * - The De Bruijn index representation would be confusing to users if we showed it.
   * - More generally, a displayed non-value (including the body of a lambda) would
   *   include code that has been transformed.
  *)
  let to_string e =
    PP.(build_string (pretty_t Prec.TopLevel e))
end

(* Misc helpers for putting together ASTs: *)
let int n = Expr.Const (Const.Integer n)
let text s = Expr.Const (Const.Text s)
let char c = Expr.Const (Const.Char c)

let prim x =
  Expr.Prim x

let prim_io x =
  Expr.PrimIO x

let assert_io = function
  | Expr.PrimIO io -> io
  | _ -> MuleErr.bug "run-time type error."

let assert_const = function
  | Expr.Const c -> c
  | _ -> MuleErr.bug "run-time type error."

let assert_int e = match assert_const e with
  | Const.Integer n -> n
  | _ -> MuleErr.bug "run-time type error."

let assert_text e = match assert_const e with
  | Const.Text s -> s
  | _ -> MuleErr.bug "run-time type error."

let assert_char c = match assert_const c with
  | Const.Char c -> c
  | _ -> MuleErr.bug "run-time type error."

let mk_record fields =
  fields
  |> List.map ~f:(fun (k, v) -> (Label.of_string k, v))
  |> Map.of_alist_exn (module Label)
  |> fun lblmap -> Expr.Record lblmap
