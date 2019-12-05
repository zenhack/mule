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

let show_cant_instantiate name binder ty =
  match name, binder, ty with
  | Some name, Some (`Quant q), `Type ty ->
      let ty = Desugared_ast_type.to_string ty in
        String.concat [
        "Mismatched types: "; name; " and "; ty; ".\n";
        begin match q with
        | `All -> String.concat [
            name; " is an `all`-bound type variable. The code must work for *all* types ";
            name; ", not just "; ty; ".";
          ]
        | `Exist -> String.concat [
            name; " is an `exist`-bound type variable. The code must work regardless of ";
            "what type it actually is, so we can't assume it's "; ty; ".";
          ]
        end
    ]
  | _ ->
    let var = match name with
      | None -> ""
      | Some v -> " " ^ v
    in
    String.concat [
      "Could not instantiate rigid type variable";
      var;
      begin match ty with
        | `Type t ->
            " with type " ^ Desugared_ast_type.to_string t
        | `Row _ ->
            (* TODO: print something helpful here. *)
            ""
      end;
      ". Rigid variables must be treated as opaque.";
    ]

let show_type_error err = match err with
  | `MismatchedKinds (l, r) ->
      "mismatched kinds: " ^ show_kind l ^ " and " ^ show_kind r
  | `OccursCheckKind ->
      "inferring kinds: occurs check failed"
  | `CantInstantiate {ci_info = TT.{vi_name; vi_binder}; ci_other}->
      show_cant_instantiate vi_name vi_binder ci_other
  | `MismatchedCtors {se_sub; se_super; se_path; se_reason} ->
      let sub_root, _super_root = se_path.MuleErr.TypePath.roots in
      begin match se_reason with
        | `Path (`Sourced src) -> String.concat [
            show_path_type_error
              ~head:src
              ~path:se_path
              ~sub:se_sub
              ~super:se_super
          ]
        | `TypeAnnotation(`WithType(Loc.{l_loc; _}, _), ty) ->
            String.concat [
              "The expression at ";
              Loc.pretty_t l_loc;
              " does not match its type annotation; its type is:";
              "\n\n";
              Desugared_ast_type.to_string (Extract.get_var_type sub_root);
              "\n\n";
              "but the annotation says it should be:";
              "\n\n";
              Desugared_ast_type.to_string ty;
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

