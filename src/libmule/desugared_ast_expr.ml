open Common_ast
module Type = Desugared_ast_type

type 'i t =
  | Embed of {
      e_path: string;
      e_value: string;
    }
  | Var of { v_var : Var.t }
  | Lam of { l_param : Var.t; l_body : 'i t }
  | App of {
      app_fn : 'i t;
      app_arg : 'i t;
    }
  | EmptyRecord
  | GetField of {
      gf_lbl : Label.t;
    }
  | UpdateType of {
      ut_lbl    : Label.t;
      ut_type   : 'i Type.t;
      ut_record : 'i t;
    }
  | UpdateVal of {
      uv_lbl : Label.t;
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
  | WithType of {
      wt_expr : 'i t;
      wt_type : 'i Type.t;
    }
  | Let of {
      let_v : Var.t;
      let_e : 'i t;
      let_body : 'i t;
    }
  | LetRec of {
      letrec_vals: (Var.t * 'i t) list;
      letrec_types: (Var.t * 'i Type.t) list;
      letrec_body: 'i t;
    }
  | Const of {
      const_val : Const.t;
    }

let rec sexp_of_t = function
  | Embed { e_path; _ } ->
      Sexp.List [Sexp.Atom "embed"; Sexp.Atom e_path]
  | Var { v_var = v } -> Sexp.Atom (Var.to_string v)
  | Lam{ l_param = v; l_body = body } ->
      Sexp.List [Sexp.Atom "fn"; Var.sexp_of_t v; sexp_of_t body]
  | App{app_fn; app_arg} ->
      Sexp.List [sexp_of_t app_fn; sexp_of_t app_arg]
  | EmptyRecord -> Sexp.Atom "{}"
  | GetField{gf_lbl; _} -> Sexp.List [
      Sexp.Atom ".";
      Label.sexp_of_t gf_lbl;
    ]
  | UpdateVal {uv_lbl} -> Sexp.List [
      Sexp.Atom ".=";
      Label.sexp_of_t uv_lbl;
    ]
  | UpdateType {ut_lbl; ut_type; ut_record} -> Sexp.List [
      Sexp.Atom ".type=";
      Label.sexp_of_t ut_lbl;
      sexp_of_t ut_record;
      Type.sexp_of_t ut_type;
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
  | WithType {wt_expr = e; wt_type = ty} ->
      Sexp.List [Sexp.Atom ":"; sexp_of_t e; Type.sexp_of_t ty]
  | Let{let_v = v; let_e = e; let_body = body} ->
      Sexp.List
        [ Sexp.Atom "let"
        ; Sexp.List [Var.sexp_of_t v; sexp_of_t e]
        ; sexp_of_t body
        ]
  | LetRec{letrec_types; letrec_vals; letrec_body} ->
      Sexp.List
        [ Sexp.Atom "letrec"
        ; Sexp.List
            [ Sexp.Atom "types"
            ; Sexp.List
                ( List.map letrec_types ~f:(fun (v, ty) ->
                      Sexp.List [Var.sexp_of_t v; Type.sexp_of_t ty]
                    )
                )
            ]
        ; Sexp.List
            [ Sexp.Atom "values"
            ; Sexp.List
                ( List.map letrec_vals ~f:(fun (var, value) ->
                      Sexp.List [Var.sexp_of_t var; sexp_of_t value]
                    )
                )
            ]
        ; sexp_of_t letrec_body
        ]
  | Const {const_val = c} ->
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
  | Let{let_v; let_e; let_body} -> Let {
      let_v;
      let_e = f let_e;
      let_body = f let_body
    }
  | LetRec{letrec_types; letrec_vals; letrec_body} ->
      LetRec {
        letrec_types;
        letrec_vals = List.map letrec_vals ~f:(fun (v, e) -> (v, f e));
        letrec_body = f letrec_body;
      }
  | UpdateType{ut_lbl; ut_type; ut_record} ->
      UpdateType {
        ut_lbl;
        ut_type;
        ut_record = f ut_record;
      }
  | Var _
  | EmptyRecord
  | GetField _
  | UpdateVal _
  | WithType _
  | Embed _
  | Const _ -> e

let rec subst_ty old new_ = function
  | WithType {wt_expr = e; wt_type = ty} ->
      WithType {
        wt_expr = subst_ty old new_ e;
        wt_type = Type.subst old new_ ty;
      }
  | e -> apply_to_kids e ~f:(subst_ty old new_)

let rec map e ~f =
  match e with
  | WithType {wt_expr = e; wt_type = ty} ->
      WithType {
        wt_type = Type.map ty ~f;
        wt_expr = map e ~f;
      }
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
  | Let{let_v; let_e; let_body} -> Let{
      let_v;
      let_e = map let_e ~f;
      let_body = map let_body ~f;
    }
  | LetRec{letrec_types; letrec_vals; letrec_body} ->
      LetRec {
        letrec_types = List.map letrec_types ~f:(fun (v, ty) -> (v, Type.map ty ~f));
        letrec_vals = List.map letrec_vals ~f:(fun (v, e) -> (v, map e ~f));
        letrec_body = map letrec_body ~f;
      }
  | UpdateType{ut_lbl; ut_type; ut_record} ->
      UpdateType {
        ut_lbl;
        ut_type = Type.map ut_type ~f;
        ut_record = map ut_record ~f;
      }
  | Var x -> Var x
  | EmptyRecord -> EmptyRecord
  | GetField x -> GetField x
  | UpdateVal x -> UpdateVal x
  | Const x -> Const x
  | Embed x -> Embed x

let rec subst: 'a t VarMap.t -> 'a t -> 'a t = fun env expr ->
  match expr with
  (* TODO: do stuff with type variables *)
  | Var {v_var = v} ->
      begin match Map.find env v with
        | None -> expr
        | Some e -> e
      end
  | Ctor{ c_lbl; c_arg } ->
      Ctor{ c_lbl; c_arg = subst env c_arg }
  | Lam {l_param; l_body} ->
      Lam {
        l_param;
        l_body = subst
            (Map.remove env l_param)
            l_body;
      }
  | App{ app_fn = f; app_arg = x } ->
      App {
        app_fn = subst env f;
        app_arg = subst env x;
      }
  | Match {cases; default} ->
      Match
        { cases =
            Map.map cases ~f:(fun (var, body) ->
              let env' = Map.remove env var in
              ( var
              , subst env' body
              )
            )
        ; default = Option.map default ~f:(function
              | (None, body) -> (None, subst env body)
              | (Some var, body) ->
                  ( Some var
                  , let env' = Map.remove env var in
                    subst env' body
                  )
            )
        }
  | ConstMatch {cm_cases; cm_default} ->
      ConstMatch
        { cm_cases = Map.map cm_cases ~f:(subst env)
        ; cm_default = subst env cm_default
        }
  | Let{let_v; let_e; let_body} ->
      Let
        { let_v
        ; let_e = subst env let_e
        ; let_body = subst (Map.remove env let_v) let_body
        }
  | LetRec _ ->
      MuleErr.bug "TODO"
  | UpdateType{ut_lbl; ut_type; ut_record} ->
      UpdateType{
        ut_lbl;
        ut_type;
        ut_record = subst env ut_record;
      }
  | Const _ | EmptyRecord | GetField _ | UpdateVal _ | WithType _ | Embed _ ->
      expr
