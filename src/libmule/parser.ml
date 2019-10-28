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
    ; "import"
    ; "embed"
    ]

(* Add source location info to a parser.
 * The argument should be a parser that returns a *function* accepting
 * the source location (as a Loc.t) of the data that it parsed. *)
let with_loc p =
  let%bind start = MParser.get_pos in
  let%bind f = p in
  let%map stop = MParser.get_pos in
  f (Loc.{start; stop})

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
let var = token (with_loc (
    let%bind name = identifier in
    if Set.mem keywords name then
      fail "reserved word"
    else
      return (fun loc -> {
          sv_var = Var.of_string name;
          sv_loc = loc;
        })
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

let constant : (Const.t, string) MParser.t = choice
    [ text_const
    ; int_const
    ; char_const
    ]

let import: (string -> string -> 'a) -> ('a, string) MParser.t
  = fun f ->
    let%bind path = kwd "import" >> text in
    let%map from = get_user_state in
    f path from

let embed = with_loc (
  let%bind e_path = kwd "embed" >> text in
  let%map e_from = get_user_state in
  fun e_loc -> Expr.Embed {e_path; e_from; e_loc}
)

let label =
  let%map {sv_var; sv_loc} = var in
  {
    sl_label = var_to_label sv_var;
    sl_loc = sv_loc;
  }

let ctor = token (with_loc (
    let%bind c = uppercase in
    let%map cs = many_chars (letter <|> char '_' <|> digit) in
    fun sl_loc -> {
      sl_label = Label.of_string (String.make 1 c ^ cs);
      sl_loc;
    }
)) <?> "constructor"

let rec typ_term = lazy (
  choice
    [ lazy_p typ_factor
    ; (ctor |>> fun c_lbl -> Type.Ctor {c_lbl})
    ; lazy_p record_type
    ; lazy_p recur_type
    ; lazy_p all_type
    ; lazy_p exist_type
    ; parens (lazy_p typ)
    ]
)
and typ_factor = lazy (
  choice
    [ with_loc (import (fun i_path i_from i_loc -> Type.Import {i_path; i_from; i_loc}))
    ; with_loc begin
      let%map v = attempt (kwd "...") >> var in
      fun rr_loc -> Type.RowRest {rr_var = v; rr_loc}
    end
    ; begin
      let%bind v = var in
      match%map many (kwd "." >> label) with
      | [] -> Type.Var {v_var = v}
      | p_lbls -> Type.Path {
          p_var = v;
          p_lbls;
        }
    end
    ]
)
and typ_app = lazy (
  let%bind t = lazy_p typ_term in
  many (lazy_p typ_term)
  |>> List.fold_left ~init:t ~f:(fun f x -> Type.App {
      app_fn = f;
      app_arg = x;
      app_loc = Loc.spanning (Type.t_loc f) (Type.t_loc x);
    })
)
and typ_annotated = lazy (
  choice
    [ with_loc begin
      let%bind anno_var = attempt (var << kwd ":") in
      let%map anno_ty = lazy_p typ_app in
      fun anno_loc -> Type.Annotated {
        anno_var;
        anno_ty;
        anno_loc;
      }
    end
    ; lazy_p typ_app
    ]
)
and recur_type = lazy (with_loc (
  kwd "rec" >>
  let%bind v = var in
  kwd "." >>
  let%map ty = lazy_p typ in
  fun recur_loc -> Type.Recur{ recur_loc; recur_var = v; recur_body = ty }
))
and quantified_type binder quantifier = lazy (with_loc (
  kwd binder >>
  let%bind vs = many1 var in
  kwd "." >>
  let%map ty = lazy_p typ in
  fun q_loc -> Type.Quant {
    q_quant = quantifier;
    q_vars = vs;
    q_body = ty;
    q_loc;
  }
))
and all_type = lazy (lazy_p (quantified_type "all" `All))
and exist_type = lazy (lazy_p (quantified_type "exist" `Exist))
and record_type = lazy (with_loc (
  let%map items = braces (comma_list (lazy_p record_item)) in
  fun r_loc -> Type.Record {r_items = items; r_loc}
)) and record_item: (Type.record_item, string) MParser.t Lazy.t = lazy (
    choice
      [ lazy_p type_decl
      ; lazy_p field_decl
      ; kwd "..." >> (var |>> fun v -> Type.Rest v)
      ]
  ) and type_decl: (Type.record_item, string) MParser.t Lazy.t = lazy (
    let%bind l = kwd "type" >> label in
    let%bind vars = many var in
    let%bind () = optional text_const in
    let%map ty = option (kwd "=" >> lazy_p typ) in
    Type.Type(l, vars, ty)
  ) and field_decl: (Type.record_item, string) MParser.t Lazy.t = lazy (
    let%bind l = label in
    let%bind ty = kwd ":" >> lazy_p typ in
    let%map () = optional text_const in
    Type.Field (l, ty)
  ) and typ_fn = lazy (
    with_loc (
      let%bind t = lazy_p typ_annotated in
      let%bind ts = option (kwd "->" >> lazy_p typ_fn) in
      match ts with
      | None -> return (fun _ -> t)
      | Some fn_ret -> return (fun fn_loc -> Type.Fn {
          fn_loc;
          fn_param = t;
          fn_ret;
        })
    )
  ) and typ_sum = lazy (
    optional (kwd "|") >>
    begin match%map sep_by1 (lazy_p typ_fn) (kwd "|") with
      | [] -> MuleErr.bug "impossible"
      | (t::ts) ->
          List.fold_right ts ~init:t ~f:(fun r l -> Type.Union{
              u_l = l;
              u_r = r;
              u_loc = Loc.spanning (Type.t_loc l) (Type.t_loc r);
            })
    end
  ) and typ = lazy (lazy_p typ_sum)

let rec expr = lazy ((with_loc (
  let%bind e = lazy_p ex0 in
  begin match%map option (kwd ":" >> lazy_p typ) with
    | Some ty -> fun wt_loc -> Expr.WithType{ wt_term = e; wt_type = ty; wt_loc }
    | None -> fun _ -> e
  end
)) <?> "expression")
and ex0 = lazy (
  let%bind t = lazy_p ex1 in
  let%map ts = many (lazy_p ex1) in
  List.fold_left ts ~init:t ~f:(fun f x -> Expr.App {
      app_fn = f;
      app_arg = x;
      app_loc = Loc.spanning (Expr.t_loc f) (Expr.t_loc x);
    })
)
and ex1 = lazy (
  let%bind old = lazy_p ex2 in
  choice
    [ with_loc begin
      let%map fields = kwd "where" >> lazy_p record_fields in
      fun up_loc -> Expr.Update {
        up_arg = old;
        up_fields = fields;
        up_loc;
      }
    end
    ; return old
    ]
)
and ex2 = lazy (
  let%bind head = lazy_p ex3 in
  many (kwd "." >> with_loc (label |>> fun l loc -> (l, loc)))
  |>> List.fold_left ~init:head ~f:(fun e (l, loc) -> Expr.GetField {
      gf_arg = e;
      gf_lbl = l;
      gf_loc = Loc.spanning (Expr.t_loc e) loc
    })
)
and ex3 = lazy (
  choice
    [ with_loc (import (fun i_path i_from i_loc -> Expr.Import {i_path; i_from; i_loc}))
    ; embed
    ; lazy_p lambda
    ; lazy_p match_expr
    ; lazy_p let_expr
    ; (var |>> fun v -> Expr.Var {v_var = v})
    ; parens (lazy_p expr)
    ; lazy_p record
    ; (ctor |>> fun c -> Expr.Ctor {c_lbl = c})
    ; with_loc (constant |>> fun n const_loc -> Expr.Const {const_val = n; const_loc})
    ]
)
and lambda = lazy ((with_loc (
  let%bind params = kwd "fn" >> many1 (lazy_p pattern) in
  let%map body = kwd "." >> lazy_p expr in
  fun lam_loc -> Expr.Lam {
    lam_params = params;
    lam_body = body;
    lam_loc;
  }
)) <?> "lambda")
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
and let_expr = lazy ((with_loc (
  let%bind _ = kwd "let" in
  let%bind bindings = comma_list1 (lazy_p binding) in
  let%map body = kwd "in" >> lazy_p expr in
  fun let_loc -> Expr.Let {
    let_binds = bindings;
    let_body = body;
    let_loc;
  }
)) <?> "let expression")
and match_expr = lazy ((with_loc (
  let%bind e = kwd "match" >> lazy_p expr in
  let%bind cases =
    kwd "with"
    >> optional (kwd "|")
    >> sep_by1 (lazy_p case) (kwd "|")
  in
  kwd "end"
  >>$ fun match_loc -> Expr.Match {
    match_arg = e;
    match_cases = cases;
    match_loc;
  }
)) <?> "match expression")
and case = lazy (
  let%bind p = lazy_p pattern in
  let%map e = kwd "->" >> lazy_p expr in
  (p, e)
)
and pattern = lazy ((
  choice
    [ with_loc (constant |>> fun n const_loc -> Pattern.Const {const_val = n; const_loc})
    ; parens (lazy_p pattern)
    ; with_loc (kwd "_" |>> fun _ w_loc -> Pattern.Wild{w_loc})
    ; with_loc begin
      let%bind v_var = var in
      let%map v_type = option (kwd ":" >> lazy_p typ) in
      fun v_loc -> Pattern.Var {v_var; v_type; v_loc}
    end
    ; with_loc begin
      let%bind lbl = ctor in
      let%map p = lazy_p pattern in
      fun c_loc -> Pattern.Ctor {c_lbl = lbl; c_arg = p; c_loc}
    end
    ]
) <?> "pattern")
and record_fields =
  lazy (braces (comma_list (lazy_p field_def)) <?> "record")
and record = lazy (with_loc(
  lazy_p record_fields
  |>> fun fields r_loc -> Expr.Record {r_fields = fields; r_loc}
))
and field_def = lazy (lazy_p type_field_def <|> lazy_p value_field_def)
and type_field_def = lazy (
  let%bind l = kwd "type" >> label in
  let%bind params = many var in
  let%bind () = optional text_const in
  let%map ty = kwd "=" >> lazy_p typ in
  `Type (l, params, ty)
)
and value_field_def = lazy (
  let%bind l = label in
  let%bind ty = option (kwd ":" >> lazy_p typ) in
  let%bind () = optional text_const in
  let%map e = kwd "=" >> lazy_p expr in
  `Value (l, ty, e)
)

let expr = Lazy.force expr
let typ = Lazy.force typ

let file p = ignorable >> p << eof
let expr_file = file expr
let type_file = file typ

let repl_line = file (option expr)
