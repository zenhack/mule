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
  let rec to_string = function
    | Var _ | LetRec _ | App _ | GetField _ | Update _ | Match _ ->
        "<non-value>"
    | Lam _ -> "<lambda>"
    | Record fields ->
        Map.to_alist fields
        |> List.map ~f:(fun (k, v) -> Label.to_string k ^ " = " ^ to_string v)
        |> String.concat ~sep:", "
        |> (fun s -> "{" ^ s ^ "}")
    | Ctor(lbl, arg) ->
        Label.to_string lbl ^ " (" ^ to_string arg ^ ")"
    | Lazy _ -> "<lazy>"
    | Const c ->
        begin match c with
          | Const.Text txt -> String.concat [
              "\"";
              String.escaped txt;
              "\"";
            ]
          | Const.Integer n ->
              Z.to_string n
          | Const.Char c -> String.concat [
              "'";
              Char.escaped c;
              "'";
            ]
        end
    | Prim _ -> "<primitive-function>"
    | PrimIO _ -> "<primitive-io>"
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
