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
  | `UnboundVar var ->
      "unbound variable: " ^ Var.to_string var
  | `MalformedType msg ->
      "malformed_type: " ^ msg
  | `MatchDesugarMismatch ->
      "Type error: constant and union patterns in the same match expression."
  | `TypeError e ->
      "Type error: " ^ show_type_error e
  | `UnreachableCases _ ->
      "Unreachable cases in match"
  | `DuplicateFields fields ->
      "Duplicate fields:\n" ^
      (fields
       |> List.map ~f:Label.to_string
       |> String.concat ~sep:",")
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
