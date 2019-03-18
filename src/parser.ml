open MParser
open Ast.Surface

let lazy_p p = return () >>= fun () -> Lazy.force p

(* Set of reserved keywords *)
let keywords = Set.of_list (module String)
  [ "fn"
  ; "rec"
  ; "type"
  ; "all"
  ; "match"
  ; "with"
  ; "end"
  ; "where"
  ; "_"
  ; "let"
  ; "in"
  ]

(* [token p] is [p] followed by optional whitespace. *)
let token p = attempt p << spaces

let kwd name =
  token (string name)

let parens p = between (kwd "(") (kwd ")") p
let braces p = between (kwd "{") (kwd "}") p

(* An identifier. Does not check if the identifier is a reserved word. *)
let identifier : (string, unit) MParser.t = (
  let id_start = lowercase <|> char '_' in
  let id_cont = letter <|> char '_' <|> digit in
  id_start
  >>= fun c -> many_chars id_cont
  |>> fun cs -> String.make 1 c ^ cs
) <?> "identifier"

(* A variable. *)
let var = token (
  identifier
  >>= fun name ->
    if Set.mem keywords name then
      fail "reserved word"
    else
      return (Ast.Var.of_string name)
)

let label =
  var |>> fun v -> Ast.Var.to_string v |> Ast.Label.of_string

let ctor = token (
  uppercase
  >>= fun c -> many_chars (letter <|> char '_' <|> digit)
  |>> fun cs -> Ast.Label.of_string (String.make 1 c ^ cs)
) <?> "constructor"

let rec typ_term = lazy (
  choice
    [ (var |>> fun v -> Type.Var v)
    ; (ctor |>> fun c -> Type.Ctor c)
    ; lazy_p record_type
    ; lazy_p recur_type
    ; lazy_p all_type
    ; parens (lazy_p typ)
    ]
) and typ_app = lazy (
  (lazy_p typ_term)
  >>= fun t -> many (lazy_p typ_term)
  |>> List.fold_left ~init:t ~f:(fun f x -> Type.App (f, x))
) and recur_type = lazy (
  kwd "rec"
  >> var
  >>= fun v -> kwd "."
  >> lazy_p typ
  |>> fun ty -> Type.Recur(v, ty)
) and all_type = lazy (
  kwd "all"
  >> many1 var
  >>= fun vs -> kwd "."
  >> lazy_p typ
  |>> fun ty -> Type.All(vs, ty)
) and record_type = lazy (
  braces (sep_end_by (lazy_p record_item) (kwd ","))
  |>> fun items -> Type.Record items
) and record_item = lazy (
  choice
    [ lazy_p field_decl
    ; kwd "..." >> (var |>> fun v -> Type.Rest v)
    ]
) and field_decl = lazy (
  label
  >>= fun l -> kwd ":"
  >> lazy_p typ
  |>> fun ty -> Type.Field (l, ty)
) and typ = lazy (
  expression
  [ [ Infix ((kwd "|" >>$ fun l r -> Type.Union (l, r)), Assoc_right) ]
  ; [ Infix ((kwd "->" >>$ fun p r -> Type.Fn(p, r)), Assoc_right) ]
  ]
  (lazy_p typ_app)
)

let rec expr = lazy ((
  lazy_p ex1
  >>= fun t -> many (lazy_p ex1)
  |>> fun ts -> List.fold_left ts ~init:t ~f:(fun f x -> Expr.App (f, x))
) <?> "expression")
and ex1 = lazy (
  lazy_p ex2
  >>= fun old -> choice
    [ (kwd "where" >> lazy_p record_fields
        |>> fun fields -> Expr.Update (old, fields))
    ; return old
    ]
)
and ex2 = lazy (
  lazy_p ex3
  >>= fun head -> many (kwd "." >> label)
  |>> List.fold_left ~init:head ~f:(fun e l -> Expr.GetField(e, l))
)
and ex3 = lazy (
  choice
    [ lazy_p lambda
    ; lazy_p match_expr
    ; lazy_p let_expr
    ; (var |>> fun v -> Expr.Var v)
    ; parens (lazy_p expr)
    ; lazy_p record
    ; (ctor |>> fun c -> Expr.Ctor c)
    ]
)
and lambda = lazy ((
  kwd "fn"
  >> many1 (lazy_p pattern)
  >>= fun params -> kwd "."
  >> lazy_p expr
  |>> fun body -> Expr.Lam (params, body)
) <?> "lambda")
and let_expr = lazy ((
  kwd "let"
  >> lazy_p pattern
  >>= fun pat -> kwd "="
  >> lazy_p expr
  >>= fun e -> kwd "in"
  >> lazy_p expr
  |>> fun body -> Expr.Let(pat, e, body)
) <?> "let expression")
and match_expr = lazy ((
  kwd "match"
  >> lazy_p expr
  >>= fun e -> kwd "with"
  >> optional (kwd "|")
  >> sep_by1 (lazy_p case) (kwd "|")
  >>= fun cases -> kwd "end"
  |>> fun _ -> Expr.Match(e, cases)
) <?> "match expression")
and case = lazy (
  lazy_p pattern
  >>= fun p -> kwd "->"
  >> lazy_p expr
  |>> fun e -> (p, e)
)
and pattern = lazy ((
  choice
    [ parens (lazy_p pattern)
    ; (kwd "_" |>> fun _ -> Pattern.Wild)
    ; (var |>> fun v -> Pattern.Var v)
    ; (ctor
        >>= fun lbl -> lazy_p pattern
        |>> fun p -> Pattern.Ctor (lbl, p)
      )
    ;
    ]
    >>= fun p -> option (kwd ":" >> lazy_p typ)
    |>> fun ty -> begin match ty with
      | Some ty' -> Pattern.Annotated(p, ty')
      | None -> p
    end
) <?> "pattern")
and record_fields = lazy ((
  braces (sep_end_by (lazy_p field_def) (kwd ","))
) <?> "record")
and record = lazy (
  lazy_p record_fields
  |>> fun fields -> Expr.Record fields
)
and field_def = lazy (
  label
  >>= fun l -> kwd "="
  >> lazy_p expr
  |>> fun e -> (l, e)
)

let expr = Lazy.force expr

let repl_line = spaces >> option expr << eof
