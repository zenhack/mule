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
    | Fn of {
        fn_info : 'i;
        fn_pvar : Var.t option;
        fn_param : 'i t;
        fn_ret : 'i t;
      }
    | Recur of {
        mu_info : 'i;
        mu_var : Var.t;
        mu_body : 'i t;
      }
    | Var of {
        v_info : 'i;
        v_var : Var.t;
      }
    | Path of {
        p_info : 'i;
        p_var : Var.t;
        p_lbls : Label.t list;
      }
    | Record of
        { r_info : 'i
        ; r_types : 'i row
        ; r_values : 'i row
        ; r_src : Surface_ast.Type.t;
        }
    | Union of {
        u_row : 'i row;
      }
    | Quant of {
        q_info : 'i;
        q_quant : quantifier;
        q_var : Var.t;
        q_body : 'i t;
      }
    | Named of {
        n_info : 'i;
        n_name : string;
      }
    | Opaque of { o_info : 'i }
    | TypeLam of {
        tl_info : 'i;
        tl_param : Var.t;
        tl_body : 'i t;
      }
    | App of {
        app_info : 'i;
        app_fn : 'i t;
        app_arg : 'i t;
      }
  and 'i row =
    ('i * (Label.t * 'i t) list * Var.t option)

  let rec subst old new_ ty = match ty with
    | Fn {fn_info; fn_pvar = Some v; fn_param; fn_ret} when Var.equal v old ->
        Fn {
          fn_info;
          fn_pvar = Some v;
          fn_param = subst old new_ fn_param;
          fn_ret;
        }
    | Fn {fn_info; fn_pvar; fn_param; fn_ret} ->
        Fn {
          fn_info;
          fn_pvar;
          fn_param = subst old new_ fn_param;
          fn_ret = subst old new_ fn_ret;
        }
    | Recur{mu_info; mu_var; mu_body} ->
        if Var.equal mu_var old then
          Recur{mu_info; mu_var; mu_body}
        else
          Recur{mu_info; mu_var; mu_body = subst old new_ mu_body}
    | Var{v_info; v_var} ->
        if Var.equal v_var old then
          new_
        else
          Var{v_info; v_var}
    | Path{p_info; p_var; p_lbls} ->
        if Var.equal p_var old then
          MuleErr.bug "TODO"
        else
          Path{p_info; p_var; p_lbls}
    | Record {r_info; r_types; r_values; r_src} ->
        Record {
          r_info;
          r_src;
          r_types = subst_row old new_ r_types;
          r_values = subst_row old new_ r_values;
        }
    | Union {u_row} ->
        Union { u_row = subst_row old new_ u_row }
    | Quant{q_info; q_quant; q_var; q_body} ->
        if Var.equal q_var old then
          Quant {q_info; q_quant; q_var; q_body}
        else
          Quant{q_info; q_quant; q_var; q_body = subst old new_ q_body}
    | Named _ -> ty
    | Opaque _ -> ty
    | TypeLam{tl_info; tl_param; tl_body} ->
        if Var.equal tl_param old then
          TypeLam{tl_info; tl_param; tl_body}
        else
          TypeLam{tl_info; tl_param; tl_body = subst old new_ tl_body}
    | App{app_info; app_fn; app_arg} ->
        App {
          app_info;
          app_fn = subst old new_ app_fn;
          app_arg = subst old new_ app_arg;
        }
  and subst_row old new_ (i, ls, maybe_v) =
    ( i
    , List.map ls ~f:(fun (l, field) -> (l, subst old new_ field))
    , match maybe_v with
    | Some v when Var.equal v old -> MuleErr.bug "TODO"
    | _ -> maybe_v
    )

  let rec sexp_of_t: 'i t -> Sexp.t = function
    | Fn{fn_pvar = None; fn_param; fn_ret; _} ->
        Sexp.List [sexp_of_t fn_param; Sexp.Atom "->"; sexp_of_t fn_ret]
    | Fn{fn_pvar = Some v; fn_param; fn_ret; _} ->
        Sexp.List
          [ Sexp.List [ Var.sexp_of_t v; Sexp.Atom ":"; sexp_of_t fn_param ]
          ; Sexp.Atom "->"
          ; sexp_of_t fn_ret
          ]
    | Recur{mu_var = v; mu_body = body; _} ->
        Sexp.List [Sexp.Atom "rec"; Var.sexp_of_t v; sexp_of_t body]
    | Var{v_var; _} ->
        Var.sexp_of_t v_var
    | Path{p_var; p_lbls; _} -> Sexp.(
        List ([Atom "."; Var.sexp_of_t p_var] @ List.map p_lbls ~f:Label.sexp_of_t)
      )
    | Record { r_info = _; r_src = _; r_types; r_values } -> Sexp.(
        List
          [ Atom "record"
          ; List [Atom "types"; sexp_of_row r_types]
          ; List [Atom "values"; sexp_of_row r_values]
          ]
      )
    | Union {u_row} ->
        Sexp.(List [Atom "union"; sexp_of_row u_row])
    | Quant {q_quant; q_var; q_body; _} ->
        Sexp.List
          [ sexp_of_quantifier q_quant
          ; Sexp.Atom(Var.to_string q_var)
          ; sexp_of_t q_body
          ]
    | TypeLam{tl_param; tl_body; _} ->
        Sexp.List [
          Sexp.Atom "lam";
          Sexp.Atom(Var.to_string tl_param);
          sexp_of_t tl_body;
        ]
    | Named{n_name; _} -> Sexp.Atom n_name
    | Opaque _ -> Sexp.Atom "<opaque>"
    | App{app_fn; app_arg; _} -> Sexp.List [
        sexp_of_t app_fn;
        sexp_of_t app_arg;
      ]
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
    | Fn{fn_info; _} -> fn_info
    | Recur{mu_info; _} -> mu_info
    | Var{v_info; _} -> v_info
    | Path{p_info; _} -> p_info
    | Record{r_info; _} -> r_info
    | Union{u_row = (x, _, _)} -> x
    | Quant{q_info; _} -> q_info
    | Named{n_info; _} -> n_info
    | Opaque {o_info; _} -> o_info
    | TypeLam{tl_info; _} -> tl_info
    | App{app_info; _} -> app_info

  let rec map ty ~f = match ty with
    | Opaque {o_info} -> Opaque { o_info = f o_info }
    | Named{n_info; n_name} ->
        Named{n_info = f n_info; n_name}
    | Fn{fn_info; fn_pvar; fn_param; fn_ret} ->
        Fn {
          fn_info = f fn_info;
          fn_pvar;
          fn_param = map fn_param ~f;
          fn_ret = map fn_ret ~f;
        }
    | Recur{ mu_info; mu_var; mu_body } ->
        Recur {
          mu_info = f mu_info;
          mu_var;
          mu_body = map mu_body ~f;
        }
    | Path{p_info; p_var; p_lbls} ->
        Path{
          p_info = f p_info;
          p_var;
          p_lbls;
        }
    | Var {v_info; v_var} ->
        Var{v_info = f v_info; v_var}
    | Record {r_info; r_types; r_values; r_src} ->
        Record
          { r_info = f r_info
          ; r_src
          ; r_types = map_row r_types ~f
          ; r_values = map_row r_values ~f
          }
    | Union {u_row} ->
        Union {u_row = map_row u_row ~f}
    | Quant {q_info; q_quant; q_var; q_body} ->
        Quant {
          q_info = f q_info;
          q_quant;
          q_var;
          q_body = map q_body ~f;
        }
    | TypeLam{tl_info; tl_param; tl_body} ->
        TypeLam {
          tl_info = f tl_info;
          tl_param;
          tl_body = map tl_body ~f;
        }
    | App{app_info; app_fn; app_arg} ->
        App {
          app_info = f app_info;
          app_fn = map app_fn ~f;
          app_arg = map app_arg ~f;
        }
  and map_row (x, fields, rest) ~f =
    ( f x
    , List.map fields ~f:(fun(l, t) -> (l, map t ~f))
    , rest
    )
end

module Expr = struct
  type 'i t =
    | Var of { v_var : Var.t }
    | Lam of { l_param : Var.t; l_body : 'i t }
    | App of {
        app_fn : 'i t;
        app_arg : 'i t;
      }
    | Fix of { fix_type : [ `Let | `Record ] }
    | EmptyRecord
    | GetField of {
        gf_strategy : [`Lazy|`Strict];
        gf_lbl : Label.t;
      }
    | Update of {
        up_level : [`Value | `Type];
        up_lbl : Label.t;
      }
    | Ctor of {
        c_lbl : Label.t;
        c_arg : 'i t;
      }
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
    | Var { v_var = v } -> Sexp.Atom (Var.to_string v)
    | Lam{ l_param = v; l_body = body } ->
        Sexp.List [Sexp.Atom "fn"; Var.sexp_of_t v; sexp_of_t body]
    | App{app_fn; app_arg} ->
        Sexp.List [sexp_of_t app_fn; sexp_of_t app_arg]
    | Fix { fix_type = `Let } -> Sexp.Atom "fix/let"
    | Fix { fix_type = `Record } -> Sexp.Atom "fix/record"
    | EmptyRecord -> Sexp.Atom "{}"
    | GetField{gf_lbl; _} -> Sexp.List [
        Sexp.Atom ".";
        Label.sexp_of_t gf_lbl;
      ]
    | Update {up_level = `Value; up_lbl} -> Sexp.List [
        Sexp.Atom ".=";
        Label.sexp_of_t up_lbl;
      ]
    | Update {up_level = `Type; up_lbl} -> Sexp.List [
        Sexp.Atom ".type=";
        Label.sexp_of_t up_lbl;
      ]
    | Ctor{c_lbl; c_arg} -> Sexp.List [
        Label.sexp_of_t c_lbl;
        sexp_of_t c_arg;
      ]
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
    | Lam {l_param; l_body} -> Lam {
        l_param;
        l_body = f l_body
      }
    | App{app_fn; app_arg} -> App {
        app_fn = f app_fn;
        app_arg = f app_arg;
      }
    | Ctor{c_lbl; c_arg} -> Ctor{c_lbl; c_arg = f c_arg}
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
    | Lam{l_param; l_body} ->
        Lam{l_param; l_body = map l_body ~f}
    | App{app_fn; app_arg}-> App {
        app_fn = map app_fn ~f;
        app_arg = map app_arg ~f;
      }
    | Ctor{c_lbl; c_arg} -> Ctor{c_lbl; c_arg = map c_arg ~f}
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
