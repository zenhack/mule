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
      braces (
        comma_sep (
          List.map fs ~f:(fun (name, e) ->
              expr (String name) ^ c ':' ^ parens (expr e)
            )
        )
      )
  | String str ->
      (* FIXME: deal with escaping properly. *)
      c '"' ^ s str ^ c '"'
  | LamE (ps, e) -> lambda ps (expr e)
  | LamS (ps, b) -> lambda ps (braces (stmts b))
and lambda ps body =
  concat [
    parens (comma_sep (List.map ps ~f:s));
    s " => ";
    body;
  ]
and stmts ss =
  end_by (c ';') (List.map ss ~f:stmt)
and stmt = function
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
