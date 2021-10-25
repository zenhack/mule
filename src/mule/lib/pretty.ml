open Common_ast
open Desugared_ast
open MuleErr_t

module TT = Typecheck_types_t



let typ t = Sexp.to_string_hum (Type.sexp_of_t t)
let expr e = Sexp.to_string_hum (Expr.sexp_of_t e)
let runtime_expr e = Sexp.to_string_hum (Runtime_ast.Expr.sexp_of_t e)

let rec show_kind = function
  | `Type -> "type"
  | `Row -> "row"
  | `Unknown -> "unknown"
  | `Arrow(l, r) ->
      String.concat ["("; show_kind l; " -> "; show_kind r; ")"]

let show_unify_error ue =
  match ue.ue_cause with
  | `MismatchedCtors(_, _) ->
      "Mismatched ctors"
  | `CantInstantiate _ ->
      "Can't instantiate"

let show_type_error : MuleErr_t.type_error -> string = function
  | `MismatchedKinds (l, r) ->
      "mismatched kinds: " ^ show_kind l ^ " and " ^ show_kind r
  | `MismatchedGuards ->
      "mismatched guards"
  | `OccursCheckKind ->
      "inferring kinds: occurs check failed"
  | `UnifyFailed ue ->
      show_unify_error ue

let show_path_error {pe_path; pe_loc; pe_problem} =
  let path = String.escaped pe_path in
  match pe_problem with
  | `AbsoluteEmbed -> String.concat [
      "Illegal embed path ";
      String.escaped path;
      " at ";
      Loc.pretty_t pe_loc;
      ": embed expressions must use relative paths ";
      "(which start with './')."
    ]
  | `IllegalChar c -> String.concat [
      "Illegal character ";
      Char.escaped c;
      " in path ";
      path;
      " at ";
      Loc.pretty_t pe_loc;
    ]
  | `BadPathPart part -> String.concat [
      "Illegal path segment ";
      String.escaped part;
      " in path ";
      path;
      " at ";
      Loc.pretty_t pe_loc;
    ]

let error = function
  | `UnboundVar Loc.{l_value; l_loc} -> String.concat [
      "Unbound variable `";
      Var.to_string l_value;
      "` at ";
      Loc.pretty_t l_loc;
    ]
  | `MalformedType msg ->
      "malformed_type: " ^ msg
  | `MatchDesugarMismatch pat -> String.concat [
      "Type error at ";
      Loc.pretty_t pat.Loc.l_loc;
      ":\n\n";
      "  this pattern matches a union, but all of the ";
      "previous patterns match constants.";
    ]
  | `TypeError e ->
      "Type error: " ^ show_type_error e
  | `UnreachableCases cases ->
      "Unreachable match cases at:\n\n" ^
      String.concat (
        List.map cases ~f:(fun (Loc.{l_loc; _}, _) ->
          "  - " ^ Loc.pretty_t l_loc ^ "\n"
        )
      )
  | `DuplicateFields (level, fields) ->
      let level_name = match level with
        | `Type -> "associated types"
        | `Value -> "record fields"
      in
      "Duplicate " ^ level_name ^ ":\n\n" ^
      (fields
       |> List.map ~f:(fun (lbl, locs) -> String.concat [
           "  - `";
           Label.to_string lbl;
           "` at:\n";
           List.sort locs ~compare:(fun
             (* Sort so that earliest occurances are first. *)
             Loc.{ start = (x, _, _); _}
             Loc.{ start = (y, _, _); _} ->
             Int.compare x y
           )
           |> List.map ~f:(fun l -> String.concat [
               "    - ";
               Loc.pretty_t l;
               "\n";
             ]
           )
           |> String.concat
         ]
       )
       |> String.concat)
  | `IncompletePattern ->
      "Incomplete pattern"
  | `IllegalAnnotatedType Loc.{l_loc; _} -> String.concat [
      "Illegal annotated type at ";
      Loc.pretty_t l_loc;
      ": only types of function parameters may be annotated.";
    ]
  | `PathError pe ->
      show_path_error pe
  | `LazyLoop ->
      "Infinite loop"

  | `NotImplemented msg ->
      "Unimplemented feature: " ^ msg
  | `Bug msg ->
      "BUG: " ^ msg

