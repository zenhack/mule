open MParser
open Ast.Surface

module Let_syntax = struct
  (* currently unused, but potentially used by the desugaring process.
  let return =
    return

  let both x y =
    x >>= fun x' -> y |>> fun y' -> (x', y')
  *)

  let map x ~f =
    x |>> f

  let bind x ~f =
    x >>= f
end

let lazy_p p = return () >>= fun () -> Lazy.force p

(* Set of reserved keywords *)
let keywords = Set.of_list (module String)
    [ "fn"
    ; "rec"
    ; "type"
    ; "all"
    ; "exist"
    ; "match"
    ; "with"
    ; "end"
    ; "where"
    ; "_"
    ; "let"
    ; "in"
    ]

let sep_start_by p sep =
  optional sep >> sep_by p sep

let sep_start_by1 p sep =
  optional sep >> sep_by1 p sep

let comment = char '#' >> many_chars (satisfy (function '\n' -> false | _ -> true))

let ignorable = skip_many (skip space <|> skip comment)

(* [token p] is [p] followed by optional whitespace & comments. *)
let token p = attempt p << ignorable

let kwd name =
  token (string name)

let parens p = between (kwd "(") (kwd ")") p
let braces p = between (kwd "{") (kwd "}") p

let comma_list p =
  sep_start_by p (kwd ",")

let comma_list1 p =
  sep_start_by1 p (kwd ",")

(* An identifier. Does not check if the identifier is a reserved word. *)
let identifier : (string, unit) MParser.t = (
  let id_start = lowercase <|> char '_' in
  let id_cont =
    letter
    <|> digit
    <|> choice (List.map ~f:char ['_';'-';'!';'?'])
  in
  let%bind c = id_start in
  let%map cs = many_chars id_cont in
  String.make 1 c ^ cs
) <?> "identifier"

(* A variable. *)
let var = token (
    let%bind name = identifier in
    if Set.mem keywords name then
      fail "reserved word"
    else
      return (Ast.Var.of_string name)
  )

let int: (Z.t, unit) MParser.t = token (
    let%bind sign = option (char '+' <|> char '-') in
    let sign =
      begin match sign with
        | Some c -> String.of_char c
        | None -> ""
      end
    in
    let%bind d = digit in
    let%bind ds = many_chars (digit <|> letter <|> char '_') in
    (* We accept the same integer formats as zarith, except that we also
     * allow underscores as visual separators. Strip those out before passing
     * them on to the library.
    *)
    let str = sign ^ String.of_char d ^ ds in
    let z_str = String.filter str ~f:(fun c -> not (Char.equal c '_')) in
    try
      return (Z.of_string z_str)
    with
      Invalid_argument _ ->
      fail ("Illegal integer literal: " ^ str)
  )

let text_legal =
  none_of "\"\\"

let escaped =
  let%bind _ = char '\\' in
  match%bind any_char with
  | '\\' -> return '\\'
  | '"' -> return '"'
  | 'n' -> return '\n'
  | 't' -> return '\t'
  | 'r' -> return '\r'
  | c -> fail ("Illegal escape sequence: \\" ^ String.of_char c)

let text: (Expr.t, unit) MParser.t = token (
    let%bind _ = char '"' in
    let%bind chars = many (text_legal <|> escaped) in
    let%map _ = char '"' in
    Expr.Text (String.of_char_list chars)
)

let label =
  var |>> Ast.var_to_label

let ctor = token (
  let%bind c = uppercase in
  let%map cs = many_chars (letter <|> char '_' <|> digit) in
  Ast.Label.of_string (String.make 1 c ^ cs)
) <?> "constructor"

let rec typ_term = lazy (
  choice
    [ lazy_p typ_factor
    ; (ctor |>> fun c -> Type.Ctor c)
    ; lazy_p record_type
    ; lazy_p recur_type
    ; lazy_p all_type
    ; lazy_p exist_type
    ; parens (lazy_p typ)
    ]
)
and typ_factor = lazy (
  let%bind v = var in
  match%map many (kwd "." >> label) with
  | [] -> Type.Var v
  | parts -> Type.Path(v, parts)
)
and typ_app = lazy (
  let%bind t = lazy_p typ_term in
  many (lazy_p typ_term)
  |>> List.fold_left ~init:t ~f:(fun f x -> Type.App (f, x))
)
and typ_annotated = lazy (
  choice
    [ begin
        let%bind v = attempt (var << kwd ":") in
        (* TODO: attach the variable to the AST somewhere. *)
        let%map ty = lazy_p typ_app in
        Type.Annotated(v, ty)
      end
    ; lazy_p typ_app
    ]
)
and recur_type = lazy (
  kwd "rec" >>
  let%bind v = var in
  kwd "." >>
  let%map ty = lazy_p typ in
  Type.Recur(v, ty)
)
and quantified_type binder quantifier = lazy (
  kwd binder >>
  let%bind vs = many1 var in
  kwd "." >>
  let%map ty = lazy_p typ in
  Type.Quant(quantifier, vs, ty)
)
and all_type = lazy (lazy_p (quantified_type "all" `All))
and exist_type = lazy (lazy_p (quantified_type "exist" `Exist))
and record_type = lazy (
  let%map items = braces (comma_list (lazy_p record_item)) in
  Type.Record items
) and record_item: (Type.record_item, unit) MParser.t Lazy.t = lazy (
  choice
    [ lazy_p type_decl
    ; lazy_p field_decl
    ; kwd "..." >> (var |>> fun v -> Type.Rest v)
    ]
) and type_decl: (Type.record_item, unit) MParser.t Lazy.t = lazy (
  let%bind l = kwd "type" >> label in
  let%bind vars = many var in
  let%bind () = optional text in
  let%map ty = option (kwd "=" >> lazy_p typ_term)
  in
  Type.Type(l, vars, ty)
) and field_decl: (Type.record_item, unit) MParser.t Lazy.t = lazy (
  let%bind l = label in
  let%bind ty = kwd ":" >> lazy_p typ in
  let%map () = optional text in
  Type.Field (l, ty)
) and typ_fn = lazy (
    begin match%map sep_by1 (lazy_p typ_annotated) (kwd "->") with
      | [t] -> t
      | ts ->
        let ts = List.rev ts in
        begin match ts with
        | [] -> failwith "impossible"
        | (t::ts) -> List.fold_left ts ~init:t ~f:(fun r l -> Type.Fn(l, r))
        end
    end
) and typ_sum = lazy (
    optional (kwd "|") >>
    begin match%map sep_by1 (lazy_p typ_fn) (kwd "|") with
    | [] -> failwith "impossible"
    | (t::ts) ->
        List.fold_right ts ~init:t ~f:(fun r l -> Type.Union(l, r))
    end
) and typ = lazy (lazy_p typ_sum)

let rec expr = lazy ((
  let%bind e = lazy_p ex0 in
  begin match%map option (kwd ":" >> lazy_p typ) with
  | Some ty -> Expr.WithType(e, ty)
  | None -> e
  end
) <?> "expression")
and ex0 = lazy (
  let%bind t = lazy_p ex1 in
  let%map ts = many (lazy_p ex1) in
  List.fold_left ts ~init:t ~f:(fun f x -> Expr.App (f, x))
)
and ex1 = lazy (
  let%bind old = lazy_p ex2 in
  choice
    [ begin
        let%map fields = kwd "where" >> lazy_p record_fields in
        Expr.Update (old, fields)
      end
    ; return old
    ]
)
and ex2 = lazy (
  let%bind head = lazy_p ex3 in
  many (kwd "." >> label)
  |>> List.fold_left ~init:head ~f:(fun e l -> Expr.GetField(e, l))
)
and ex3 = lazy (
  choice
    [ lazy_p lambda
    ; lazy_p match_expr
    ; lazy_p let_expr
    ; text
    ; (var |>> fun v -> Expr.Var v)
    ; parens (lazy_p expr)
    ; lazy_p record
    ; (ctor |>> fun c -> Expr.Ctor c)
    ; (int |>> fun n -> Expr.Integer n)
    ]
)
and lambda = lazy ((
  let%bind params = kwd "fn" >> many1 (lazy_p pattern) in
  let%map body = kwd "." >> lazy_p expr in
  Expr.Lam (params, body)
) <?> "lambda")
and binding = lazy (
  choice
    [ begin
        let%bind v = kwd "type" >> var in
        let%bind params = many var in
        let%map ty = kwd "=" >> lazy_p typ in
        `BindType(v, params, ty)
      end
    ; begin
        let%bind pat = lazy_p pattern in
        let%map e    = kwd "=" >> lazy_p expr in
        `BindVal(pat, e)
      end
    ]
)
and let_expr = lazy ((
  let%bind _ = kwd "let" in
  let%bind bindings = comma_list1 (lazy_p binding) in
  let%map body = kwd "in" >> lazy_p expr in
  Expr.Let(bindings, body)
) <?> "let expression")
and match_expr = lazy ((
    let%bind e = kwd "match" >> lazy_p expr in
    let%bind cases =
      kwd "with"
      >> optional (kwd "|")
      >> sep_by1 (lazy_p case) (kwd "|")
    in
    kwd "end"
    >>$ Expr.Match(e, cases)
  ) <?> "match expression")
and case = lazy (
  let%bind p = lazy_p pattern in
  let%map e = kwd "->" >> lazy_p expr in
  (p, e)
)
and pattern = lazy ((
  choice
    [ (int |>> fun n -> Pattern.Integer n)
    ; parens (lazy_p pattern)
    ; (kwd "_" |>> fun _ -> Pattern.Wild)
    ; begin
        let%bind v = var in
        match%map option (kwd ":" >> lazy_p typ) with
        | Some ty -> Pattern.Var (v, Some ty)
        | None -> Pattern.Var (v, None)
      end
    ; begin
       let%bind lbl = ctor in
       let%map p = lazy_p pattern in
       Pattern.Ctor (lbl, p)
      end
    ]
) <?> "pattern")
and record_fields =
  lazy (braces (comma_list (lazy_p field_def)) <?> "record")
and record = lazy (
  lazy_p record_fields
  |>> fun fields -> Expr.Record fields
)
and field_def = lazy (lazy_p type_field_def <|> lazy_p value_field_def)
and type_field_def = lazy (
  let%bind l = kwd "type" >> label in
  let%bind params = many var in
  let%bind () = optional text in
  let%map ty = kwd "=" >> lazy_p typ in
  `Type (l, params, ty)
)
and value_field_def = lazy (
  let%bind l = label in
  let%bind ty = option (kwd ":" >> lazy_p typ) in
  let%bind () = optional text in
  let%map e = kwd "=" >> lazy_p expr in
  `Value (l, ty, e)
)

let expr = Lazy.force expr

let repl_line = ignorable >> option expr << eof
