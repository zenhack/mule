open MParser
open Ast
open Ast.Surface

type 'a parser_t = ('a, unit) MParser.t

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

let located p =
  let%bind start = get_pos in
  let%bind value = p in
  let%map stop = get_pos in
  Located.at (Located.mk_range start stop) value

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
let identifier : string parser_t = (
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
      return (Var.of_string name)
  )

let int_const: (Const.t, unit) MParser.t = token (
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
      return (Const.Integer (Z.of_string z_str))
    with
      Invalid_argument _ ->
        fail ("Illegal integer literal: " ^ str)
  )

let text_legal =
  none_of "\"\\"

let char_legal =
  none_of "'\\"

let escaped =
  let%bind _ = char '\\' in
  match%bind any_char with
  | '\\' -> return '\\'
  | '"' -> return '"'
  | '\'' -> return '\''
  | 'n' -> return '\n'
  | 't' -> return '\t'
  | 'r' -> return '\r'
  | c -> fail ("Illegal escape sequence: \\" ^ String.of_char c)

let text_const: (Const.t, unit) MParser.t = token (
    let%bind _ = char '"' in
    let%bind chars = many (text_legal <|> escaped) in
    let%map _ = char '"' in
    Const.Text (String.of_char_list chars)
  )

let char_const: (Const.t, unit) MParser.t = token (
    let%bind _ = char '\'' in
    let%bind c = char_legal <|> escaped in
    let%map _ = char '\'' in
    Const.Char c
  )

let constant : (Const.t, unit) MParser.t = choice
    [ text_const
    ; int_const
    ; char_const
    ]

let label =
  var |>> Ast.var_to_label

let ctor = token (
    let%bind c = uppercase in
    let%map cs = many_chars (letter <|> char '_' <|> digit) in
    Label.of_string (String.make 1 c ^ cs)
  ) <?> "constructor"

let rec typ_term: Type.t parser_t Lazy.t = lazy (
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
  let%bind lvar = located var in
  match%map many (kwd "." >> located label) with
  | [] -> Type.Var (Located.value lvar)
  | parts -> Type.Path(lvar, parts)
)
and typ_app: Type.t parser_t Lazy.t = lazy (
  let%bind t = located (lazy_p typ_term) in
  let%map parts = many (located (lazy_p typ_term)) in
  List.fold_left parts ~init:t ~f:(fun f x ->
      Located.spaning f x (Type.App (f, x))
    )
  |> Located.value
)
and typ_annotated: Type.t parser_t Lazy.t = lazy (
  choice
    [ begin
      let%bind v = located (attempt (var << kwd ":")) in
      (* TODO: attach the variable to the AST somewhere. *)
      let%map ty = located (lazy_p typ_app) in
      Type.Annotated(v, ty)
    end
    ; lazy_p typ_app
    ]
)
and recur_type: Type.t parser_t Lazy.t = lazy (
  kwd "rec" >>
  let%bind v = located var in
  kwd "." >>
  let%map ty = located (lazy_p typ) in
  Type.Recur(v, ty)
)
and quantified_type binder quantifier = lazy (
  let%bind lbinder = located (kwd binder) in
  let%bind vs = many1 (located var) in
  kwd "." >>
  let%map ty = located (lazy_p typ) in
  Type.Quant
    ( Located.at (Located.loc lbinder) quantifier
    , vs
    , ty
    )
)
and all_type = lazy (lazy_p (quantified_type "all" `All))
and exist_type = lazy (lazy_p (quantified_type "exist" `Exist))
and record_type = lazy (
  let%map items = braces (comma_list (located (lazy_p record_item))) in
  Type.Record items
) and record_item: (Type.record_item, unit) MParser.t Lazy.t = lazy (
    choice
      [ lazy_p type_decl
      ; lazy_p field_decl
      ; kwd "..." >> (var |>> fun v -> Type.Rest v)
      ]
  ) and type_decl: Type.record_item parser_t Lazy.t = lazy (
    let%bind l = kwd "type" >> located label in
    let%bind vars = many (located var) in
    let%bind () = optional text_const in
    let%map ty = option (kwd "=" >> located (lazy_p typ))
    in
    Type.Type(l, vars, ty)
  ) and field_decl: (Type.record_item, unit) MParser.t Lazy.t = lazy (
    let%bind l = located label in
    let%bind ty = kwd ":" >> located (lazy_p typ) in
    let%map () = optional text_const in
    Type.Field (l, ty)
  ) and typ_fn: Type.t parser_t Lazy.t = lazy (
    begin match%map sep_by1 (located (lazy_p typ_annotated)) (kwd "->") with
      | [t] ->
          Located.value t
      | ts ->
          let ts = List.rev ts in
          begin match ts with
            | [] -> failwith "impossible"
            | (t::ts) ->
                Located.value
                  (List.fold_left ts ~init:t ~f:(fun r l ->
                       Located.spaning l r (Type.Fn(l, r))
                     )
                  )
          end
    end
  ) and typ_sum = lazy (
    optional (kwd "|") >>
    begin match%map sep_by1 (located (lazy_p typ_fn)) (kwd "|") with
      | [] -> failwith "impossible"
      | (t::ts) ->
          Located.value
            (List.fold_right ts ~init:t ~f:(fun r l ->
                 Located.spaning l r (Type.Union(l, r))
               )
            )
    end
  ) and typ = lazy (lazy_p typ_sum)

let rec expr = lazy ((
    let%bind e = located (lazy_p ex0) in
    begin match%map option (kwd ":" >> located (lazy_p typ)) with
      | Some ty -> Expr.WithType(e, ty)
      | None -> Located.value e
    end
  ) <?> "expression")
and ex0 = lazy (
  let%bind t = located (lazy_p ex1) in
  let%map ts = many (located (lazy_p ex1)) in
  List.fold_left ts ~init:t ~f:(fun f x -> Located.spaning f x (Expr.App (f, x)))
  |> Located.value
)
and ex1 = lazy (
  let%bind old = located (lazy_p ex2) in
  choice
    [ begin
      let%map fields = kwd "where" >> lazy_p record_fields in
      Expr.Update (old, fields)
    end
    ; return (Located.value old)
    ]
)
and ex2: Expr.t parser_t Lazy.t = lazy (
  let%bind head = located (lazy_p ex3) in
  let%map lbls = many (kwd "." >> located label) in
  List.fold_left
    lbls
    ~init:head
    ~f:(fun e l -> Located.spaning e l (Expr.GetField(e, l)))
  |> Located.value
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
    ; (constant |>> fun n -> Expr.Const n)
    ]
)
and lambda = lazy ((
    let%bind params = kwd "fn" >> many1 (located (lazy_p pattern)) in
    let%map body = kwd "." >> located (lazy_p expr) in
    Expr.Lam (params, body)
  ) <?> "lambda")
and binding = lazy (
  choice
    [ begin
      let%bind v = kwd "type" >> located var in
      let%bind params = many (located var) in
      let%map ty = kwd "=" >> located (lazy_p typ) in
      `BindType(v, params, ty)
    end
    ; begin
      let%bind pat = located (lazy_p pattern) in
      let%map e    = kwd "=" >> located (lazy_p expr) in
      `BindVal(pat, e)
    end
    ]
)
and let_expr = lazy ((
    let%bind _ = kwd "let" in
    let%bind bindings = comma_list1 (located (lazy_p binding)) in
    let%map body = kwd "in" >> located (lazy_p expr) in
    Expr.Let(bindings, body)
  ) <?> "let expression")
and match_expr = lazy ((
    let%bind e = kwd "match" >> located (lazy_p expr) in
    let%bind cases =
      kwd "with"
      >> optional (kwd "|")
      >> sep_by1 (located (lazy_p case)) (kwd "|")
    in
    kwd "end"
    >>$ Expr.Match(e, cases)
  ) <?> "match expression")
and case = lazy (
  let%bind p = located (lazy_p pattern) in
  let%map e = kwd "->" >> located (lazy_p expr) in
  (p, e)
)
and pattern = lazy ((
    choice
      [ (constant |>> fun n -> Pattern.Const n)
      ; parens (lazy_p pattern)
      ; (kwd "_" |>> fun _ -> Pattern.Wild)
      ; begin
        let%bind v = located var in
        match%map option (kwd ":" >> located (lazy_p typ)) with
        | Some ty -> Pattern.Var (v, Some ty)
        | None -> Pattern.Var (v, None)
      end
      ; begin
        let%bind lbl = located ctor in
        let%map p = located (lazy_p pattern) in
        Pattern.Ctor (lbl, p)
      end
      ]
  ) <?> "pattern")
and record_fields =
  lazy (braces (comma_list (located (lazy_p field_def))) <?> "record")
and record = lazy (
  lazy_p record_fields
  |>> fun fields -> Expr.Record fields
)
and field_def = lazy (lazy_p type_field_def <|> lazy_p value_field_def)
and type_field_def = lazy (
  let%bind l = kwd "type" >> located label in
  let%bind params = many (located var) in
  let%bind () = optional text_const in
  let%map ty = kwd "=" >> located (lazy_p typ) in
  `Type (l, params, ty)
)
and value_field_def = lazy (
  let%bind l = located label in
  let%bind ty = option (kwd ":" >> located (lazy_p typ)) in
  let%bind () = optional text_const in
  let%map e = kwd "=" >> located (lazy_p expr) in
  `Value (l, ty, e)
)

let expr = Lazy.force expr
let typ = Lazy.force typ

let file p = ignorable >> p << eof
let expr_file = file expr
let type_file = file typ

let repl_line = file (option expr)
