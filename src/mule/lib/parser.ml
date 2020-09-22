open MParser
open Common_ast
open Surface_ast

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
let keywords = Set.of_list (module String) [
    "fn";
    "rec";
    "type";
    "all";
    "exist";
    "match";
    "with";
    "end";
    "where";
    "_";
    "let";
    "in";
    "import";
    "embed";
  ]

(* Add source location info to a parser.
 * The argument should be a parser that returns a *function* accepting
 * the source location (as a Loc.t) of the data that it parsed. *)
let with_loc p =
  let%bind start = MParser.get_pos in
  let%bind f = p in
  let%map (off, line, char) = MParser.get_pos in
  (* We want an inclusive range, so step back a character: *)
  let stop = (off, line, char-1) in
  f (Loc.{start; stop})

let located p =
  with_loc (
    let%map l_value = p in
    fun l_loc -> Loc.{l_loc; l_value}
  )

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
let brackets p = between (kwd "[") (kwd "]") p

let comma_list p =
  sep_start_by p (kwd ",")

let comma_list1 p =
  sep_start_by1 p (kwd ",")

(* An identifier. Does not check if the identifier is a reserved word. *)
let identifier : (string, string) MParser.t = (
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
let var = token (located(
    let%bind name = identifier in
    if Set.mem keywords name then
      fail "reserved word"
    else
      return (Var.of_string name)
  ))

let int_const: (Const.t, string) MParser.t = token (
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

let text = token (
    let%bind _ = char '"' in
    let%bind chars = many (text_legal <|> escaped) in
    let%map _ = char '"' in
    String.of_char_list chars
  )

let text_const: (Const.t, string) MParser.t =
  let%map str = text in
  Const.Text str

let char_const: (Const.t, string) MParser.t = token (
    let%bind _ = char '\'' in
    let%bind c = char_legal <|> escaped in
    let%map _ = char '\'' in
    Const.Char c
  )

let constant : (Const.t, string) MParser.t = choice [
    text_const;
    int_const;
    char_const;
  ]

let import: (Import.t, string) MParser.t
  = let%bind i_path = kwd "import" >> located text in
  let%map i_from = get_user_state in
  Import.{i_path; i_from}

let embed = (
  let%bind e_path = kwd "embed" >> text in
  let%map e_from = get_user_state in
  Expr.Embed {e_path; e_from}
)

let label =
  let%map v = var in
  Loc.map v ~f:var_to_label

let ctor = token (located (
    let%bind c = uppercase in
    let%map cs = many_chars (letter <|> char '_' <|> digit) in
    Label.of_string (String.make 1 c ^ cs)
  )) <?> "constructor"

let rec typ_term = lazy (
  choice [
    lazy_p typ_factor;
    located (ctor |>> fun c_lbl -> Type.Ctor {c_lbl});
    lazy_p record_type;
    lazy_p recur_type;
    lazy_p all_type;
    lazy_p exist_type;
    parens (lazy_p typ);
  ]
)
and typ_factor = lazy (
  choice [
    located begin
      let%map rest = attempt (kwd "...") >> lazy_p typ in
      Type.RowRest rest
    end;
    located begin
      let%bind head = choice [
          (var |>> fun v -> `Var v);
          (located import |>> (fun i -> `Import i));
        ]
      in
      match%map many (kwd "." >> label) with
      | [] -> begin match head with
          | `Var v -> Type.Var {v_var = v}
          | `Import i -> Type.Import i.Loc.l_value
        end
      | p_lbls -> Type.Path {
          p_var = head;
          p_lbls;
        }
    end;
  ]
)
and typ_app = lazy (
  let%bind t = lazy_p typ_term in
  many (lazy_p typ_term)
  |>> List.fold_left ~init:t ~f:(fun f x -> Loc.{
      l_value = Type.App {
          app_fn = f;
          app_arg = x;
        };
      l_loc = Loc.spanning f.l_loc x.l_loc;
    })
)
and typ_annotated = lazy (
  choice [
    located begin
      let%bind anno_var = attempt (var << kwd ":") in
      let%map anno_ty = lazy_p typ_app in
      Type.Annotated {
        anno_var;
        anno_ty;
      }
    end;
    lazy_p typ_app;
  ]
)
and recur_type = lazy (located (
    kwd "rec" >>
    let%bind v = var in
    kwd "." >>
    let%map ty = lazy_p typ in
    Type.Recur{ recur_var = v; recur_body = ty }
  ))
and quantifier = function
  | `All -> located (kwd "all" >>$ `All)
  | `Exist -> located (kwd "exist" >>$ `Exist)
and quantified_type q = lazy (located (
    let%bind q_quant = quantifier q in
    let%bind vs = many1 (lazy_p q_binding) in
    kwd "." >>
    let%map ty = lazy_p typ in
    Type.Quant {
      q_quant;
      q_vars = vs;
      q_body = ty;
    }
  ))
and q_binding = lazy (
  choice
    [ var |>> (fun v -> (v, None))
    ; parens (
          let%bind v = var in
          kwd ":>" >>
          let%map ty = lazy_p typ in
          (v, Some ty)
        )
    ]
)
and all_type = lazy (lazy_p (quantified_type `All))
and exist_type = lazy (lazy_p (quantified_type `Exist))
and record_type = lazy (located (
    let%map r_items = braces (comma_list (lazy_p record_item)) in
    Type.Record {r_items}
  ))
and record_item: (Type.record_item Loc.located, string) MParser.t Lazy.t = lazy (
  choice [
    lazy_p type_decl;
    lazy_p field_decl;
    located (kwd "..." >> (lazy_p typ |>> fun t -> Type.Rest t));
  ]
)
and type_decl: (Type.record_item Loc.located, string) MParser.t Lazy.t = lazy (located (
    let%bind l = kwd "type" >> label in
    let%bind vars = many var in
    let%bind () = optional text_const in
    let%map ty = option (kwd "=" >> lazy_p typ) in
    Type.Type(l, vars, ty)
  ))
and field_decl: (Type.record_item Loc.located, string) MParser.t Lazy.t = lazy (located (
    let%bind l = label in
    let%bind ty = kwd ":" >> lazy_p typ in
    let%map () = optional text_const in
    Type.Field (l, ty)
  ))
and typ_fn = lazy (
  let%bind t = lazy_p typ_annotated in
  let%map ts = option (kwd "->" >> lazy_p typ_fn) in
  match ts with
  | None -> t
  | Some fn_ret -> Loc.{
      l_value = Type.Fn {
          fn_param = t;
          fn_ret;
        };
      l_loc = spanning t.l_loc fn_ret.l_loc;
    }
)
and typ_sum = lazy (
  optional (kwd "|") >>
  begin match%map sep_by1 (lazy_p typ_fn) (kwd "|") with
    | [] -> MuleErr.bug "impossible"
    | (t::ts) ->
        List.fold_right ts ~init:t ~f:(fun r l -> Loc.{
            l_value = Type.Union{
                u_l = l;
                u_r = r;
              };
            l_loc = spanning l.l_loc r.l_loc;
          })
  end
)
and typ = lazy (lazy_p typ_sum)

let rec expr = lazy ((
  let%bind e = lazy_p ex0 in
  begin match%map option (kwd ":" >> lazy_p typ) with
    | Some ty -> Loc.{
        l_value = Expr.WithType{ wt_term = e; wt_type = ty };
        l_loc = spanning e.l_loc ty.l_loc;
      }
    | None -> e
  end
) <?> "expression")
and ex0 = lazy (
  let%bind t = lazy_p ex1 in
  let%map ts = many (lazy_p ex1) in
  List.fold_left ts ~init:t ~f:(fun f x -> Loc.{
      l_value = Expr.App {
          app_fn = f;
          app_arg = x;
        };
      l_loc = spanning f.l_loc x.l_loc;
    })
)
and ex1 = lazy (
  let%bind old = lazy_p ex2 in
  choice [
    located begin
      let%map fields = kwd "where" >> lazy_p record_fields in
      Expr.Update {
        up_arg = old;
        up_fields = fields;
      }
    end;
    return old;
  ]
)
and ex2 = lazy (
  let%bind quotes = many (lazy_p quote) in
  let%bind head = lazy_p ex3 in
  let%map e =
    many (kwd "." >> label)
    |>> List.fold_left
      ~init:head
      ~f:(fun e l -> Loc.{
          l_value = Expr.GetField {
              gf_arg = e;
              gf_lbl = l;
            };
          l_loc = spanning e.l_loc l.l_loc;
        })
  in
  List.fold_right quotes ~init:e ~f:(fun q body ->
    let f e = match q.Loc.l_value with
      | `Quote -> Expr.Quote e
      | `Unquote -> Expr.Unquote e
      | `UnquoteSplice -> Expr.UnquoteSplice e
    in
    Loc.{
      l_loc = spanning q.l_loc body.l_loc;
      l_value = f body;
    }
  )
)
and ex3 = lazy (
  choice [
    located (import |>> (fun i -> Expr.Import i));
    located embed;
    lazy_p lambda;
    lazy_p match_expr;
    lazy_p let_expr;
    located (var |>> fun v -> Expr.Var {v_var = v});
    located (brackets (comma_list (lazy_p expr))
             |>> fun l -> Expr.List {l_elts = l});
    parens (lazy_p expr);
    lazy_p record;
    located (ctor |>> fun c -> Expr.Ctor {c_lbl = c});
    located (constant |>> fun n -> Expr.Const {const_val = n});
  ]
)
and quote = lazy (located (choice [
    (kwd "`" >>$ `Quote);
    (kwd "~@" >>$ `UnquoteSplice);
    (kwd "~" >>$ `Unquote);
  ]))
and lambda = lazy ((located (
    let%bind params = kwd "fn" >> many1 (lazy_p pattern) in
    let%map body = kwd "." >> lazy_p expr in
    Expr.Lam {
      lam_params = params;
      lam_body = body;
    }
  )) <?> "lambda")
and binding = lazy (
  choice [
    located begin
      let%bind v = kwd "type" >> var in
      let%bind params = many var in
      let%map ty = kwd "=" >> lazy_p typ in
      `BindType(v, params, ty)
    end;
    located begin
      let%bind pat = lazy_p pattern in
      let%map e    = kwd "=" >> lazy_p expr in
      `BindVal(pat, e)
    end;
  ]
)
and let_expr = lazy ((located (
    let%bind _ = kwd "let" in
    let%bind bindings = comma_list1 (lazy_p binding) in
    let%map body = kwd "in" >> lazy_p expr in
    Expr.Let {
      let_binds = bindings;
      let_body = body;
    }
  )) <?> "let expression")
and match_expr = lazy ((located (
    let%bind e = kwd "match" >> lazy_p expr in
    let%bind cases =
      kwd "with"
      >> optional (kwd "|")
      >> sep_by1 (lazy_p case) (kwd "|")
    in
    kwd "end"
    >>$ Expr.Match {
      match_arg = e;
      match_cases = cases;
    }
  )) <?> "match expression")
and case = lazy (
  let%bind p = lazy_p pattern in
  let%map e = kwd "->" >> lazy_p expr in
  (p, e)
)
and pattern = lazy ((
  choice [
    located (constant |>> fun n -> Pattern.Const {const_val = n});
    parens (lazy_p pattern);
    located (kwd "_" >>$ Pattern.Wild);
    located begin
      let%bind v_var = var in
      let%map v_type = option (kwd ":" >> lazy_p typ) in
      Pattern.Var {v_var; v_type}
    end;
    located begin
      let%bind lbl = ctor in
      let%map p = lazy_p pattern in
      Pattern.Ctor {c_lbl = lbl; c_arg = p}
    end;
  ]
) <?> "pattern")
and record_fields =
  lazy (braces (comma_list (lazy_p field_def)) <?> "record")
and record = lazy (located (
    lazy_p record_fields
    |>> fun fields -> Expr.Record {r_fields = fields}
  ))
and field_def = lazy (lazy_p type_field_def <|> lazy_p value_field_def)
and type_field_def = lazy (located (
    let%bind l = kwd "type" >> label in
    let%bind params = many var in
    let%bind () = optional text_const in
    let%map ty = kwd "=" >> lazy_p typ in
    `Type (l, params, ty)
  ))
and value_field_def = lazy (located(
    let%bind l = label in
    let%bind ty = option (kwd ":" >> lazy_p typ) in
    let%bind () = optional text_const in
    let%map e = kwd "=" >> lazy_p expr in
    `Value (l, ty, e)
  ))

let expr = Lazy.force expr
let typ = Lazy.force typ

let file p = ignorable >> p << eof
let expr_file = file expr
let type_file = file typ

let repl_line = file (option expr)
