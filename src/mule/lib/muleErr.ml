include MuleErr_t
open Common_ast

let show_ctor = function
  | `Named name -> Typecheck_types_t.string_of_typeconst_name name
  | `Extend lbl -> "row containing " ^ Label.to_string lbl

let show_op = function
  | `Graft -> "graft"
  | `Merge -> "merge"
  | `Raise -> "raise"
  | `Weaken -> "weaken"

let rec show_kind = function
  | `Type -> "type"
  | `Row -> "row"
  | `Unknown -> "unknown"
  | `Arrow(l, r) ->
      String.concat ["("; show_kind l; " -> "; show_kind r; ")"]

let show_type_error err = match err with
  | `MismatchedCtors (l, r) ->
      "mismatched type constructors: " ^ show_ctor l ^ " and " ^ show_ctor r
  | `MismatchedKinds (l, r) ->
      "mismatched kinds: " ^ show_kind l ^ " and " ^ show_kind r
  | `OccursCheckKind ->
      "inferring kinds: occurs check failed"
  | `PermissionErr `Graft ->
      "could not instatiate rigid type variable"
  | `PermissionErr op ->
      "permission error during " ^ show_op op

let show_path_error {pe_path; pe_problem} =
  let path = String.escaped pe_path in
  match pe_problem with
  | `AbsoluteEmbed ->
      "Illegal embed path: " ^ path ^ "; embeds must use " ^
      "relative paths."
  | `IllegalChar c ->
      "Illegal character " ^ Char.escaped c ^ " in path " ^ path
  | `BadPathPart part ->
      "Illegal path segment " ^ String.escaped part ^ " in path " ^ path

let show = function
  | `UnboundVar Loc.{l_value; l_loc} -> String.concat [
      "Unbound variable `";
      Var.to_string l_value;
      "` at ";
      Loc.pretty_t l_loc;
    ]
  | `MalformedType msg ->
      "malformed_type: " ^ msg
  | `MatchDesugarMismatch ->
      "Type error: constant and union patterns in the same match expression."
  | `TypeError e ->
      "Type error: " ^ show_type_error e
  | `UnreachableCases _ ->
      "Unreachable cases in match"
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
  | `EmptyMatch ->
      "Empty match expression."
  | `IncompletePattern ->
      "Incomplete pattern"
  | `IllegalAnnotatedType _ ->
      "Illegal annotated type: only types of function parameters may be annotated."
  | `PathError pe ->
      show_path_error pe
  | `LazyLoop ->
      "Infinite loop"
  | `Bug msg ->
      "BUG: " ^ msg

let throw e =
  if Config.always_print_stack_trace () then
    begin
      Stdio.print_endline ("Mule Exception: " ^ show e);
      Caml.Printexc.print_raw_backtrace
        Caml.stdout
        (Caml.Printexc.get_callstack 25);
    end;
  raise (MuleExn e)

let bug msg =
  throw (`Bug msg)
