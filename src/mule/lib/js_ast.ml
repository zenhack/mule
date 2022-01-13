open Fmt
include Js_ast_t

let rec expr = function
  | Var v -> s v
  | Call (f, args) ->
      parens (expr f) ^ parens (comma_sep (List.map args ~f:expr))
  | Index(obj, idx) ->
      parens (expr obj) ^ brackets (expr idx)
  | Array es ->
      brackets (comma_sep (List.map es ~f:expr))
  | Object fs ->
      braces (comma_sep (List.map fs ~f:field))
  | String str ->
      s (Yojson.to_string (`String str))
  | Int n ->
      s (Yojson.to_string (`Int n))
  | BigInt n ->
      s (Z.to_string n) ^ c 'n'
  | Lam (ps, `E e) -> lambda ps (expr e)
  | Lam (ps, `S b) -> lambda ps (braces (stmts b))
  | Null -> s "null"
  | RecordUpdate(old, fs) ->
      braces (
        comma_sep ((s "..." ^ (parens (expr old))) :: List.map ~f:field fs)
      )
and field (name, e) =
  expr (String name) ^ c ':' ^ parens (expr e)
and lambda ps body =
  concat [
    parens (comma_sep (List.map ps ~f:s));
    s " => ";
    body;
  ]
and stmts ss =
  end_by (c ';') (List.map ss ~f:stmt)
and stmt = function
  | VarDecl (v, e) ->
      s "var " ^ s v ^ s " = " ^ expr e
  | Return e ->
      s "return " ^ expr e
  | Switch {sw_scrutinee; sw_cases; sw_default} ->
      concat [
        s "switch";
        parens (expr sw_scrutinee);
        braces (
          concat [
            List.map sw_cases ~f:(fun (e, b) ->
              concat [
                s "case ";
                expr e;
                c ':';
                stmts b;
              ]
            )
            |> concat;
            begin match sw_default with
              | None -> empty
              | Some b -> s "default: " ^ stmts b
            end;
          ]
        );
      ]
