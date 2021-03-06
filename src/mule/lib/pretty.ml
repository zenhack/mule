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

let show_path_type_error ~head ~path ~sub ~super =
  match path.TypePath.segs, super with
  | [], DT.Record _ ->
      String.concat [
        Loc.pretty_t head.Loc.l_loc;
        begin match head.Loc.l_value with
          | `Var v ->  String.concat [
              ": variable ";
              Var.to_string v
            ]
          | `Import Surface_ast.Import.{i_path; _} -> String.concat [
              "import ";
              String.escaped i_path.Loc.l_value;
            ]
        end;
        " is not a record; it cannot have associated types.";
      ]
  | _ ->
      String.concat [
        "Mismatched type constructors: ";
        Desugared_ast_type.to_string sub;
        " is not a subtype of ";
        Desugared_ast_type.to_string super;
      ]

let show_type_annotation_err (src, ty) =
  let what = match src with
    | `WithType(Loc.{l_loc; _}, _) ->
        `Fragment ("expression", l_loc)
    | `Pattern(Loc.{l_loc; l_value}, _) ->
        `Fragment ("variable `" ^ Var.to_string l_value ^ "`", l_loc)
    | `RecordVal(Loc.{l_loc; l_value}, _, _) ->
        `Fragment ("record field `" ^ Label.to_string l_value ^ "`", l_loc)
    | `Msig -> `Msig
    | `Main -> `Main
  in
  begin match what with
    | `Fragment(what, where) -> String.concat [
        "The "; what; " at "; Loc.pretty_t where;
        " does not match its type annotation.\n";
        "The annotation says its type should be:";
      ]
    | `Msig -> String.concat [
        "The file does not match it's signature (.msig).\n";
        "The signature file says the type should be:";
      ]
    | `Main -> String.concat [
        "The file does not have the required type. The entrypoint to a ";
        "program for this target must have type:";
      ]
  end
  ^ "\n\n" ^ Desugared_ast_type.to_string ty

let expr_loc expr =
  Desugared_ast_expr.get_src_expr expr
  |> Option.map ~f:(fun Loc.{l_loc; _} -> Loc.pretty_t l_loc)
  |> Option.value ~default:"<TODO>"

let show_getfield_error (_, expr) ~path:TypePath.{segs; _} ~actual =
  let rec which_record_part = function
    | `RecordPart p :: _ -> p
    | _ :: ps -> which_record_part ps
    | [] ->
        MuleErr.bug (
          "TypePath for record field access doesn't include a "
          ^ "`RecordPart segment."
        )
  in
  let expr_loc = expr_loc expr in
  let rec go = function
    | [] -> String.concat [
        "The expression at "; expr_loc; " is not a record; you cannot ";
        "access its fields with the `.` operator.\n";
        "For reference, its actual type is:\n\n";
        Desugared_ast_type.to_string actual;
      ]
    | `RowLabel lbl :: ps -> String.concat [
        "The record at "; expr_loc; " does not have ";
        begin match which_record_part ps with
          | `Type -> "an associated type";
          | `Value -> "a field"
        end;
        " named "; Label.to_string lbl; " it cannot be accessed using";
        " the `.` operator.\n";
        "For reference, its actual type is:\n\n";
        Desugared_ast_type.to_string actual;
      ]
    | `RowTail :: rest -> go rest
    | ps ->
        MuleErr.bug (
          "Unexpected TypePath for `GetField reason: "
          ^ Sexp.to_string_hum (List.sexp_of_t TypePath.sexp_of_seg ps)
        )
  in
  go segs

let show_cant_instantiate
    {ci_info = TT.{vi_ident; vi_binder}; ci_other; ci_path; ci_reason}
  =
  let name = match vi_ident with
    | `VarName name -> name
    | _ -> "<generated type variable>"
  in
  match vi_ident, vi_binder, ci_other with
  | _, Some (`Quant q), `Type ty ->
      let sub, super = ci_path.TypePath.roots in
      let sub = sub |> Extract.get_var_type in
      let sub_str = sub |> Desugared_ast_type.to_string in
      let super = super |> Extract.get_var_type in
      let super_str = super |> Desugared_ast_type.to_string in
      let ty = Desugared_ast_type.to_string ty in
      String.concat [
        begin match NonEmpty.rev ci_reason with
          | (`TypeAnnotation ta, _) -> String.concat [
              show_type_annotation_err ta;
              "\n\n";
              "but its actual type is:";
              "\n\n";
              sub_str;
              "\n\n";
            ]
          | (`GetField gf, _) ->
              show_getfield_error gf ~path:ci_path ~actual:sub
          | _ -> String.concat [
              "Mismatched types: `"; sub_str ; "` and `"; super_str ; "`.\n";
            ]
        end;
        "We can't set the type variable `"; name; "` to "; ty; ", because ";
        begin match q with
          | `All -> String.concat [
              "`"; name; "` is an `all`-bound type variable. The code must work for *all* types ";
              "`"; name; "`, not just "; ty; ".";
            ]
          | `Exist -> String.concat [
              "`"; name; "` is an `exist`-bound type variable. The code must work regardless of ";
              "what type it actually is, so we can't assume it's "; ty; ".";
            ]
        end;
      ]
  | `EmptyRecordVals, _, `Row {row_fields; _}
  | `EmptyRecordTypes, _, `Row {row_fields; _}
  | `EmptyUnion, _, `Row {row_fields; _} ->
      String.concat [
        "Missing ";
        begin match vi_ident with
          | `EmptyRecordVals -> "record fields"
          | `EmptyRecordTypes -> "associated types"
          | `EmptyUnion -> "union tags"
          | _ -> MuleErr.bug "impossible"
        end;
        ": ";
        List.map row_fields ~f:(fun (lbl, _) -> Label.to_string lbl)
        |> String.concat ~sep:", ";
      ]
  | _ ->
      String.concat [
        "Could not instantiate rigid type variable ";
        name;
        begin match ci_other with
          | `Type t ->
              " with type " ^ Desugared_ast_type.to_string t
          | `Row _ ->
              (* TODO: print something helpful here. *)
              ""
        end;
        ". Rigid variables must be treated as opaque.";
      ]

let show_type_error err = match err with
  | `UnguardedRecursiveType t -> String.concat [
      "Unguarded recursive type `"; t; "`. Recursively-bound type variables ";
      "must be \"guarded\" by a union, record, or function.";
    ]
  | `MismatchedKinds (l, r) ->
      "mismatched kinds: " ^ show_kind l ^ " and " ^ show_kind r
  | `OccursCheckKind ->
      "inferring kinds: occurs check failed"
  | `CantInstantiate ci ->
      show_cant_instantiate ci
  | `MismatchedCtors {se_sub; se_super; se_path; se_reason} ->
      let sub_root, _super_root = se_path.TypePath.roots in
      let sub_root = Extract.get_var_type sub_root in
      begin match NonEmpty.rev se_reason with
        | (`Path (`Sourced src), _) -> String.concat [
            show_path_type_error
              ~head:src
              ~path:se_path
              ~sub:se_sub
              ~super:se_super
          ]
        | (`TypeAnnotation ta, _) -> String.concat [
            show_type_annotation_err ta;
            "\n\n";
            "but its actual type is:";
            "\n\n";
            Desugared_ast_type.to_string sub_root;
          ]
        | (`ApplyFn(_, _, argtype), _) -> String.concat [
            "The expression at "; "<TODO>"; " is being applied to a ";
            "value of type:";
            "\n\n";
            Extract.get_var_type argtype |> Desugared_ast_type.to_string;
            "\n\n";
            "but its type is:";
            "\n\n";
            Desugared_ast_type.to_string sub_root;
            "\n\n";
            "The type:";
            "\n\n";
            Desugared_ast_type.to_string se_sub;
            "\n\n";
            "is not a subtype of:";
            "\n\n";
            Desugared_ast_type.to_string se_super;
          ]
        | (`RecordUpdate(_lbl, record, _new), _) ->
            String.concat [
              "The expression at "; expr_loc record; " is not a record; it cannot be ";
              "updated using `where`.\n";
              "For reference, its actual type is:\n\n";
              Desugared_ast_type.to_string se_sub;
            ]
        | (`GetField gf, _) -> show_getfield_error gf ~path:se_path ~actual:se_sub
        | (`Unspecified, _) ->
            String.concat [
              "<TODO>: Get rid of unspecified reasons.\n";
              "Mismatched type constructors: ";
              Desugared_ast_type.to_string se_sub;
              " is not a subtype of ";
              Desugared_ast_type.to_string se_super;
            ]
        | _ ->
            String.concat [
              "Mismatched type constructors: ";
              Desugared_ast_type.to_string se_sub;
              " is not a subtype of ";
              Desugared_ast_type.to_string se_super;
            ]
      end

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

