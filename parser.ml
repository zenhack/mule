open MParser
open Ast.Surface

module StrSet = Set.Make(String)

let lazy_p p = return () >>= fun () -> Lazy.force p

(* Set of reserved keywords *)
let keywords = StrSet.of_list
  [ "fn"
  ; "rec"
  ; "match"
  ; "with"
  ; "end"
  ; "where"
  ; "_"
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

let ctor = token (
  uppercase
  >>= fun c -> many_chars (letter <|> char '_' <|> digit)
  |>> fun cs -> Ast.Label (String.make 1 c ^ cs)
) <?> "constructor"

let rec expr = lazy ((
  lazy_p ex1
  >>= fun t -> many (lazy_p ex1)
  |>> fun ts -> List.fold_left (fun f x -> Expr.App ((), f, x)) t ts
) <?> "expression")
and ex1 = lazy (
  lazy_p ex2
  >>= fun old -> choice
    [ (kwd "where" >> lazy_p record_fields
        |>> fun fields -> Expr.Update ((), old, fields))
    ; return old
    ]
)
and ex2 = lazy (
  lazy_p ex3
  >>= fun head -> many (kwd "." >> label)
  |>> List.fold_left (fun e l -> Expr.GetField((), e, l)) head
)
and ex3 = lazy (
  choice
    [ lazy_p lambda
    ; lazy_p match_expr
    ; (var |>> fun v -> Expr.Var ((), v))
    ; parens (lazy_p expr)
    ; lazy_p record
    ; (ctor |>> fun c -> Expr.Ctor (((), c)))
    ]
)
and lambda = lazy ((
  kwd "fn"
  >> var
  >>= fun param -> kwd "."
  >> lazy_p expr
  |>> fun body -> Expr.Lam ((), param, body)
) <?> "lambda")
and match_expr = lazy ((
  kwd "match"
  >> lazy_p expr
  >>= fun e -> kwd "with"
  >> optional (kwd "|")
  >> sep_by1 (lazy_p case) (kwd "|")
  >>= fun cases -> kwd "end"
  |>> fun _ -> Expr.Match((), e, cases)
) <?> "match expression")
and case = lazy (
  lazy_p pattern
  >>= fun p -> kwd "->"
  >> lazy_p expr
  |>> fun e -> (p, e)
)
and pattern = lazy ((
  choice
    [ (kwd "_" |>> fun _ -> Pattern.Wild ())
    ; (var |>> fun v -> Pattern.Var((), v))
    ; (ctor
        >>= fun lbl -> lazy_p pattern
        |>> fun p -> Pattern.Ctor ((), lbl, p)
      )
    ;
    ]
) <?> "pattern")
and record_fields = lazy ((
  braces (sep_end_by (lazy_p field_def) (kwd ","))
) <?> "record")
and record = lazy (
  lazy_p record_fields
  |>> fun fields -> Expr.Record ((), fields)
)
and field_def = lazy (
  label
  >>= fun l -> kwd "="
  >> lazy_p expr
  |>> fun e -> (l, e)
)

let expr = Lazy.force expr

let repl_line = spaces >> option expr << eof
