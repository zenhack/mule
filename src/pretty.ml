open Ast
open Ast.Desugared

module Format = Caml.Format

module Doc : sig
  type t

  val s : string -> t
  val concat : ?sep:t -> t list -> t
  val hbox : t -> t
  val vbox : ?indent:int -> t -> t
  val hvbox : ?indent:int -> t -> t
  val cut : t
  val empty : t

  val to_string : t -> string
end = struct
  type box_type =
    [ `H
    | `V of int
    | `HV of int
    ]

  type t =
    [ `Box of box_type * t
    | `Join of t list
    | `Cut
    | `String of string
    | `Empty
    ]

  let s str = `String str
  let concat ?sep docs =
    match sep with
    | Some s -> `Join (List.intersperse ~sep:s docs)
    | None -> `Join docs
  let hbox doc = `Box(`H, doc)
  let vbox ?indent:(n=2) doc = `Box(`V n, doc)
  let hvbox ?indent:(n=2) doc = `Box(`HV n, doc)
  let cut = `Cut
  let empty = `Empty

  let rec interp ppf = function
    | `Box (ty, doc) ->
        begin
          begin match ty with
          | `H -> Format.pp_open_hbox ppf ()
          | `V n -> Format.pp_open_vbox ppf n
          | `HV n -> Format.pp_open_hvbox ppf n
          end;
          interp ppf doc;
          Format.pp_close_box ppf ()
        end
    | `Join docs ->
        List.iter docs ~f:(interp ppf)
    | `Cut ->
        Format.pp_print_cut ppf ()
    | `String s ->
        Format.pp_print_string ppf s
    | `Empty ->
        ()

  let to_string doc =
    let buf = Buffer.create 0 in
    let ppf = Format.formatter_of_buffer buf in
    interp ppf doc;
    Format.pp_print_flush ppf ();
    Buffer.contents buf
end

let prec = function
  | `Top -> -1000
  | `Type -> -50
  | `App | `AppL -> 0
  | `AppR -> 1
  | `FnR | `Fn -> 10
  | `FnL -> 20
  | `Alt -> 30
  | `WhereL -> 39
  | `Where -> 40

let is_left = function
  | `FnL | `AppL | `WhereL -> true
  | _ -> false

let maybe_parens cond doc =
  if cond then
    Doc.concat
      [ Doc.s "("
      ; doc
      ; Doc.s ")"
      ]
  else
    doc

let op_parens parent child doc =
  maybe_parens (prec child < prec parent) doc

let binder_parens parent doc =
  maybe_parens (is_left parent) doc

let rec typ p =
  let open Type in
  function
  | Var (_, v) ->
      Doc.s (Ast.Var.to_string v)
  | Fn (_, f, x) ->
      op_parens p `Fn
        (Doc.concat
          [ typ `FnL f
          ; Doc.s " -> "
          ; typ `FnR x
          ])
  | Recur (_, v, body) ->
      binder_parens p
        (Doc.concat
          [ Doc.s "rec "
          ; Doc.s (Ast.Var.to_string v)
          ; Doc.s ". "
          ; typ `Top body
          ])
  | Record (_, fields, rest) ->
      Doc.concat
        [ Doc.s "{"
        ; List.map fields ~f:(fun (lbl, ty) ->
            Doc.concat
              [ Doc.s (Ast.Label.to_string lbl)
              ; Doc.s " : "
              ; typ `Top ty
              ]
          )
          |> Doc.concat ~sep:(Doc.s ", ")
        ; (match rest with
            | Some v -> Doc.s (", ..." ^ Ast.Var.to_string v)
            | None -> Doc.empty)
        ; Doc.s "}"
        ]
  | Union (_, ctors, rest) ->
      op_parens p `Alt
        (Doc.concat
          [ Doc.concat ~sep:(Doc.s " | ")
              (List.map ctors ~f: (fun (lbl, ty) -> Doc.concat
                [ Doc.s (Ast.Label.to_string lbl)
                ; Doc.s " "
                ; typ `AppR ty
                ]))
          ; match rest with
              | Some v -> Doc.concat [ Doc.s " | ..."; Doc.s (Ast.Var.to_string v) ]
              | None -> Doc.empty
          ]
        )
  | Quant(_, q, var, _, body) ->
      let qstr = match q with
        | `All -> "all"
        | `Exist -> "exist"
      in
      binder_parens p
        (Doc.concat
          [ Doc.s qstr
          ; Doc.s " "
          ; Doc.s (Var.to_string var)
          ; Doc.s ". "
          ; typ `Top body
          ])

let rec expr p = function
  | Expr.Var var ->
      Doc.s (Var.to_string var)
  | Expr.Ctor (name, e) ->
      op_parens p `App
        (Doc.concat
          [ Doc.s (Label.to_string name)
          ; Doc.s " "
          ; expr `AppR e
          ])
  | Expr.Lam (var, body) ->
      binder_parens p
        (Doc.concat
          [ Doc.s "fn "
          ; Doc.s (Var.to_string var)
          ; Doc.s ". "
          ; expr `Top body
          ])
  | Expr.App (f, x) ->
      op_parens p `App
        (Doc.concat
          [ expr `AppL f
          ; Doc.s " "
          ; expr `AppR x
          ])
  | Expr.EmptyRecord ->
      Doc.s "{}"
  | Expr.Update lbl ->
      Doc.s ("_." ^ Label.to_string lbl ^ ":=_")
  | Expr.GetField lbl ->
      Doc.s ("_." ^ Label.to_string lbl)
  | Expr.WithType ty ->
      op_parens p `Type
        (Doc.concat [Doc.s "_ : "; typ `Type ty])
  | Expr.Let (v, e, body) ->
      binder_parens p
        (Doc.vbox ~indent:0
          (Doc.concat
            [ Doc.s "let "
            ; Doc.s (Var.to_string v)
            ; Doc.s " = "
            ; Doc.hvbox (expr `Top e)
            ; Doc.s " in"
            ; Doc.cut
            ; Doc.hvbox (expr `Top body)
            ])
        )
  | Expr.LetRec (bindings, body) ->
      binder_parens p
        (Doc.vbox ~indent:0
          (Doc.concat
            [ Doc.s "let "
            ; Doc.vbox ~indent:1
                (Doc.concat
                  (List.map bindings ~f:(fun (var, e) ->
                    (Doc.concat
                      [ Doc.s (Var.to_string var)
                      ; Doc.s " = "
                      ; Doc.hvbox (expr `Top e)
                      ; Doc.cut
                      ]))))
            ; Doc.s " in"
            ; Doc.cut
            ; Doc.hvbox (expr `Top body)
            ])
          )
  | Expr.Match {cases; default} ->
      let branches =
        List.append
          (Map.to_alist cases
            |> List.map ~f:(fun (lbl, (v, e)) ->
                (Doc.concat
                  [ Doc.s "| "
                  ; Doc.s (Label.to_string lbl)
                  ; Doc.s " "
                  ; Doc.s (Var.to_string v)
                  ; Doc.s " -> "
                  ; Doc.hvbox (expr `Top e)
                  ])
            ))
            [ Doc.concat (match default with
                | None -> [Doc.empty]
                | Some (None, e) ->
                    [ Doc.s "| _ -> "
                    ; Doc.hvbox (expr `Top e)
                    ]
                | Some (Some v, e) ->
                    [ Doc.s "| "
                    ; Doc.s (Var.to_string v)
                    ; Doc.s " -> "
                    ; Doc.hvbox (expr `Top e)
                    ])
            ]
      in
      Doc.vbox
        (Doc.concat
          [ Doc.cut
          ; Doc.s "match-lam"
          ; List.map branches ~f:(fun b -> Doc.concat [Doc.cut; Doc.hbox b])
            |> Doc.concat
          ; Doc.cut
          ; Doc.s "end"
          ])

let rec runtime_expr p =
  let open Ast.Runtime.Expr in
  function
  | Lazy _ -> Doc.s "<lazy>"
  | Vec arr ->
      Doc.concat
        [ Doc.s "["
        ; Doc.concat
          ~sep:(Doc.s ", ")
          (Array.to_list arr
            |> List.map ~f:(runtime_expr `Top))
        ; Doc.s "]"
        ]
  | Var v -> Doc.s ("v" ^ Int.to_string v)
  | Lam(_, _, body) ->
      binder_parens p
        (Doc.concat [Doc.s "fn. "; runtime_expr `Top body])
  | App(f, x) ->
      op_parens p `App
        (Doc.concat
          [ runtime_expr `AppL f
          ; Doc.s " "
          ; runtime_expr `AppR x
          ])
  | Record r -> Doc.concat
      [ Doc.s "{"
      ; Map.to_alist r
          |> List.map ~f:(fun (k, v) -> Doc.concat ~sep:(Doc.s " ")
              [ Doc.s (Label.to_string k)
              ; Doc.s "="
              ; runtime_expr `Top v
              ]
          )
          |> Doc.concat ~sep:(Doc.s ", ")
      ; Doc.s "}"
      ]
  | GetField label ->
      Doc.s ("_." ^ Label.to_string label)
  | Update {old; label; field} ->
      op_parens p `Where
        (Doc.concat ~sep:(Doc.s " ")
          [ runtime_expr `WhereL old
          ; Doc.s "where {"
          ; Doc.s (Label.to_string label)
          ; Doc.s "="
          ; runtime_expr `Top field
          ; Doc.s "}"
          ])
  | Ctor (label, arg) ->
      op_parens p `App
        (Doc.concat
          [ Doc.s (Label.to_string label)
          ; Doc.s " "
          ; runtime_expr `AppR arg
          ]
        )
  | Match {cases; default} ->
    let branches =
      List.append
        (Map.to_alist cases
          |> List.map
              ~f:(fun (lbl, f) -> Doc.concat
                  [ Doc.s "| "
                  ; Doc.s (Label.to_string lbl)
                  ; Doc.s " -> "
                  ; Doc.hvbox
                      (Doc.concat
                        [ Doc.cut
                        ; runtime_expr `Top f
                        ])
                  ]
              )
        )
        [ match default with
            | None -> Doc.empty
            | Some f -> Doc.hbox (Doc.concat
                [ Doc.s "| _ ->"
                ; Doc.hvbox
                    (Doc.concat
                      [ Doc.cut
                      ; runtime_expr `Top f
                      ])
                ])
        ]
    in
    Doc.vbox
     (Doc.concat
        [ Doc.cut
        ; Doc.s "match _ with"
        ; List.map branches ~f:(fun b -> Doc.concat [Doc.cut; Doc.hbox b])
          |> Doc.concat
        ; Doc.cut
        ; Doc.s "end"
        ])

let typ t = Doc.to_string (typ `Top t)
let expr e = Doc.to_string (expr `Top e)
let runtime_expr e = Doc.to_string (runtime_expr `Top e)
