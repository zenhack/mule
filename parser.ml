open MParser

module StrSet = Set.Make(String)

let lazy_p p = return () >>= fun () -> Lazy.force p

(* Set of reserved keywords *)
let keywords = StrSet.of_list
  [ "fn"
  ; "rec"
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
    if StrSet.mem name keywords then
      fail "reserved word"
    else
      return (Ast.Var name)
)

let label =
  var |>> fun (Ast.Var name) -> Ast.Label name

let rec expr = lazy ((
  lazy_p term
  >>= fun t -> many (lazy_p term)
  |>> fun ts -> List.fold_left (fun f x -> Ast.Expr.App ((), f, x)) t ts
) <?> "expression")
and term = lazy (
  choice
    [ lazy_p lambda
    ; (var |>> fun v -> Ast.Expr.Var ((), v))
    ; parens (lazy_p expr)
    ; lazy_p record
    ]
  >>= fun head -> many (kwd "." >> label)
  |>> List.fold_left (fun e l -> Ast.Expr.GetField((), e, l)) head
)
and lambda = lazy ((
  kwd "fn"
  >> var
  >>= fun param -> kwd "."
  >> lazy_p expr
  |>> fun body -> Ast.Expr.Lam ((), param, body)
) <?> "lambda")
and record = lazy ((
  braces (sep_end_by (lazy_p field_def) (kwd ","))
  |>> fun fields -> Ast.Expr.Record ((), fields)
) <?> "record")
and field_def = lazy (
  label
  >>= fun l -> kwd "="
  >> lazy_p expr
  |>> fun e -> (l, e)
)

let expr = Lazy.force expr

let repl_line = spaces >> option expr << eof
