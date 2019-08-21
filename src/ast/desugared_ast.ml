open Common_ast

module Kind = struct
  type maybe_kind =
    [ `Unknown
    | `Type
    | `Row
    | `Arrow of maybe_kind * maybe_kind
    ]
  [@@deriving sexp_of]

  type t =
    [ `Type
    | `Row
    | `Arrow of t * t
    ]
  [@@deriving sexp_of]
end

module Type = struct
  type quantifier = [ `All | `Exist ]

  let sexp_of_quantifier = function
    | `All -> Sexp.Atom "all"
    | `Exist -> Sexp.Atom "exist"

  type 'i t =
    | Fn of ('i * Var.t option * 'i t * 'i t)
    | Recur of ('i * Var.t * 'i t)
    | Var of ('i * Var.t)
    | Path of ('i * Var.t * Label.t list)
    | Record of
        { r_info : 'i
        ; r_types : 'i row
        ; r_values : 'i row
        ; r_src : Surface_ast.Type.t;
        }
    | Union of 'i row
    | Quant of ('i * quantifier * Var.t * 'i t)
    | Named of ('i * string)
    | Opaque of 'i
    | TypeLam of ('i * Var.t * 'i t)
    | App of ('i * 'i t * 'i t)
  and 'i row =
    ('i * (Label.t * 'i t) list * Var.t option)

  let rec subst old new_ = function
    | Fn (i, Some v, p, r) when Var.equal v old ->
        Fn(i, Some v, (subst old new_ p), r)
    | Fn (i, maybe_v, p, r) ->
        Fn(i, maybe_v, (subst old new_ p), (subst old new_ r))
    | Recur(i, v, body) ->
        if Var.equal v old then
          Recur(i, v, body)
        else
          Recur(i, v, subst old new_ body)
    | Var(i, v) ->
        if Var.equal v old then
          new_
        else
          Var(i, v)
    | Path(i, v, ls) ->
        if Var.equal v old then
          MuleErr.bug "TODO"
        else
          Path(i, v, ls)
    | Record {r_info; r_types; r_values; r_src} ->
        Record {
          r_info;
          r_src;
          r_types = subst_row old new_ r_types;
          r_values = subst_row old new_ r_values;
        }
    | Union row ->
        Union(subst_row old new_ row)
    | Quant(i, q, v, body) ->
        if Var.equal v old then
          Quant(i, q, v, body)
        else
          Quant(i, q, v, subst old new_ body)
    | Named(i, s) -> Named(i, s)
    | Opaque i -> Opaque i
    | TypeLam(i, v, body) ->
        if Var.equal v old then
          TypeLam(i, v, body)
        else
          TypeLam(i, v, subst old new_ body)
    | App(i, f, x) ->
        App(i, subst old new_ f, subst old new_ x)
  and subst_row old new_ (i, ls, maybe_v) =
    ( i
    , List.map ls ~f:(fun (l, field) -> (l, subst old new_ field))
    , match maybe_v with
    | Some v when Var.equal v old -> MuleErr.bug "TODO"
    | _ -> maybe_v
    )

  let rec sexp_of_t: 'i t -> Sexp.t = function
    | Fn(_, None, param, ret) ->
        Sexp.List [sexp_of_t param; Sexp.Atom "->"; sexp_of_t ret]
    | Fn(_, Some v, param, ret) ->
        Sexp.List
          [ Sexp.List [ Var.sexp_of_t v; Sexp.Atom ":"; sexp_of_t param ]
          ; Sexp.Atom "->"
          ; sexp_of_t ret
          ]
    | Recur(_, v, body) ->
        Sexp.List [Sexp.Atom "rec"; Var.sexp_of_t v; sexp_of_t body]
    | Var(_, v) ->
        Var.sexp_of_t v
    | Path(_, v, ls) -> Sexp.(
        List ([Atom "."; Var.sexp_of_t v] @ List.map ls ~f:Label.sexp_of_t)
      )
    | Record { r_info = _; r_src = _; r_types; r_values } -> Sexp.(
        List
          [ Atom "record"
          ; List [Atom "types"; sexp_of_row r_types]
          ; List [Atom "values"; sexp_of_row r_values]
          ]
      )
    | Union row ->
        Sexp.(List [Atom "union"; sexp_of_row row])
    | Quant (_, q, v, t) ->
        Sexp.List [sexp_of_quantifier q; Sexp.Atom(Var.to_string v); sexp_of_t t]
    | TypeLam(_, v, body) ->
        Sexp.List [Sexp.Atom "lam"; Sexp.Atom(Var.to_string v); sexp_of_t body]
    | Named(_, name) -> Sexp.Atom name
    | Opaque _ -> Sexp.Atom "<opaque>"
    | App(_, f, x) -> Sexp.List [sexp_of_t f; sexp_of_t x]
  and sexp_of_row (_, fields, rest) =
    let fields =
      List.map fields ~f:(fun (l, t) ->
          Sexp.List [Label.sexp_of_t l; sexp_of_t t]
        )
    in
    match rest with
    | Some v -> Sexp.List (fields @ [Sexp.Atom ("..." ^ Var.to_string v)])
    | None -> Sexp.List fields

  let get_info = function
    | Fn(x, _, _, _) -> x
    | Recur(x, _, _) -> x
    | Var(x, _) -> x
    | Path(x, _, _) -> x
    | Record {r_info; _} -> r_info
    | Union(x, _, _) -> x
    | Quant(x, _, _, _) -> x
    | Named(x, _) -> x
    | Opaque x -> x
    | TypeLam(x, _, _) -> x
    | App(x, _, _) -> x

  let rec map ty ~f = match ty with
    | Opaque x -> Opaque (f x)
    | Named(x, s) ->
        Named(f x, s)
    | Fn(x, v, l, r) ->
        Fn(f x, v, map l ~f, map r ~f)
    | Recur(x, v, body) ->
        Recur(f x, v, map body ~f)
    | Path(x, v, ls) ->
        Path(f x, v, ls)
    | Var (x, v) ->
        Var(f x, v)
    | Record {r_info; r_types; r_values; r_src} ->
        Record
          { r_info = f r_info
          ; r_src
          ; r_types = map_row r_types ~f
          ; r_values = map_row r_values ~f
          }
    | Union row ->
        Union(map_row row ~f)
    | Quant(x, q, v, body) ->
        Quant(f x, q, v, map body ~f)
    | TypeLam(x, v, body) ->
        TypeLam(f x, v, map body ~f)
    | App(x, fn, arg) ->
        App(f x, map fn ~f, map arg ~f)
  and map_row (x, fields, rest) ~f =
    ( f x
    , List.map fields ~f:(fun(l, t) -> (l, map t ~f))
    , rest
    )
end

module Expr = struct
  type 'i t =
    | Var of Var.t
    | Lam of (Var.t * 'i t)
    | App of ('i t * 'i t)
    | Fix of [ `Let | `Record ]
    | EmptyRecord
    | GetField of ([`Lazy|`Strict] * Label.t)
    | Update of ([`Value | `Type] * Label.t)
    | Ctor of (Label.t * 'i t)
    | Match of {
        cases: (Var.t * 'i t) LabelMap.t;
        default: (Var.t option * 'i t) option;
      }
    | ConstMatch of
        { cm_cases : 'i t ConstMap.t
        ; cm_default: 'i t
        }
    | WithType of 'i Type.t
    | Witness of 'i Type.t
    | Let of (Var.t * 'i t * 'i t)
    | LetType of ((Var.t * 'i Type.t) list * 'i t)
    | Const of Const.t

  let rec sexp_of_t = function
    | Var v -> Sexp.Atom (Var.to_string v)
    | Lam(v, body) ->
        Sexp.List [Sexp.Atom "fn"; Var.sexp_of_t v; sexp_of_t body]
    | App(f, x) ->
        Sexp.List [sexp_of_t f; sexp_of_t x]
    | Fix `Let -> Sexp.Atom "fix/let"
    | Fix `Record -> Sexp.Atom "fix/record"
    | EmptyRecord -> Sexp.Atom "{}"
    | GetField(_, l) -> Sexp.List [Sexp.Atom "."; Label.sexp_of_t l]
    | Update(`Value, l) -> Sexp.List [Sexp.Atom ".="; Label.sexp_of_t l]
    | Update(`Type, l) -> Sexp.List [Sexp.Atom ".type="; Label.sexp_of_t l]
    | Ctor(l, arg) -> Sexp.List [Label.sexp_of_t l; sexp_of_t arg]
    | Match {cases; default} ->
        let cs =
          [ Sexp.Atom "match"
          ; Map.sexp_of_m__t
              (module Label)
              (fun (v, e) ->
                 Sexp.List [Var.sexp_of_t v; sexp_of_t e]
              )
              cases
          ]
        in
        begin match default with
          | None -> Sexp.List cs
          | Some (maybe_v, def) ->
              let v = match maybe_v with
                | Some v -> Var.sexp_of_t v
                | None -> Sexp.Atom "_"
              in
              Sexp.List (cs @ [Sexp.List [v; sexp_of_t def]])
        end
    | ConstMatch {cm_cases; cm_default} ->
        Sexp.List
          [ Sexp.Atom "match/const"
          ; Map.sexp_of_m__t (module Const) sexp_of_t cm_cases
          ; Sexp.List [Sexp.Atom "_"; sexp_of_t cm_default]
          ]
    | WithType ty ->
        Sexp.List [Sexp.Atom ":"; Type.sexp_of_t ty]
    | Witness ty ->
        Sexp.List [Sexp.Atom "type"; Type.sexp_of_t ty]
    | Let(v, e, body) ->
        Sexp.List
          [ Sexp.Atom "let"
          ; Sexp.List [Var.sexp_of_t v; sexp_of_t e]
          ; sexp_of_t body
          ]
    | LetType(binds, body) ->
        Sexp.List
          [ Sexp.Atom "let-type"
          ; Sexp.List
              (List.map binds ~f:(fun (v, ty) ->
                   Sexp.List [Var.sexp_of_t v; Type.sexp_of_t ty]
                 )
              )
          ; sexp_of_t body
          ]
    | Const c ->
        Const.sexp_of_t c

  let apply_to_kids e ~f = match e with
    | Lam (v, body) -> Lam (v, f body)
    | App(x, y) -> App(f x, f y)
    | Ctor(l, arg) -> Ctor(l, f arg)
    | Match {cases; default} ->
        Match
          { cases = Map.map cases ~f:(fun (k, v) -> (k, f v))
          ; default = Option.map default ~f:(fun (k, v) -> (k, f v))
          }
    | ConstMatch {cm_cases; cm_default} ->
        ConstMatch
          { cm_cases = Map.map cm_cases ~f
          ; cm_default = f cm_default
          }
    | Let(v, e, body) -> Let(v, f e, f body)
    | LetType(binds, body) -> LetType(binds, f body)
    | Var _
    | Fix _
    | EmptyRecord
    | GetField _
    | Update _
    | WithType _
    | Witness _
    | Const _ -> e

  let rec subst_ty old new_ = function
    | WithType ty -> WithType (Type.subst old new_ ty)
    | Witness ty -> Witness (Type.subst old new_ ty)
    | e -> apply_to_kids e ~f:(subst_ty old new_)

  let rec map e ~f =
    match e with
    | WithType ty -> WithType (Type.map ty ~f)
    | Witness ty -> Witness (Type.map ty ~f)
    | LetType(binds, body) ->
        LetType
          ( List.map binds ~f:(fun (k, v) -> (k, Type.map v ~f))
          , map body ~f
          )
    | Lam(v, body) -> Lam(v, map body ~f)
    | App(x, y) -> App(map x ~f, map y ~f)
    | Ctor(l, arg) -> Ctor(l, map arg ~f)
    | Match {cases; default} ->
        let f' (k, v) = (k, map v ~f) in
        Match
          { cases = Map.map cases ~f:f'
          ; default = Option.map default ~f:f'
          }
    | ConstMatch {cm_cases; cm_default} ->
        ConstMatch
          { cm_cases = Map.map cm_cases ~f:(map ~f)
          ; cm_default = map cm_default ~f
          }
    | Let(v, e, body) -> Let(v, map e ~f, map body ~f)
    | Var x -> Var x
    | Fix x -> Fix x
    | EmptyRecord -> EmptyRecord
    | GetField x -> GetField x
    | Update x -> Update x
    | Const x -> Const x
end
