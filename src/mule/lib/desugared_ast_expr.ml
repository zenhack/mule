include Desugared_ast_expr_t
open Common_ast
module Type = Desugared_ast_type

let rec sexp_of_t = function
  | Embed { e_path; _ } ->
      Sexp.List [Sexp.Atom "embed"; Sexp.Atom e_path]
  | Var { v_var = v; _ } -> Sexp.Atom (Var.to_string v)
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
  | Match b -> Sexp.List [
      Sexp.Atom "match";
      sexp_of_branch b;
    ]
  | WithType {wt_expr = e; wt_type = ty} ->
      Sexp.List [Sexp.Atom ":"; sexp_of_t e; Type.sexp_of_t ty]
  | Let{let_v = v; let_e = e; let_body = body} ->
      Sexp.List [
        Sexp.Atom "let";
        Sexp.List [Var.sexp_of_t v; sexp_of_t e];
        sexp_of_t body;
      ]
  | LetRec{letrec_types; letrec_vals; letrec_body} ->
      Sexp.List [
        Sexp.Atom "letrec";
        Sexp.List [
          Sexp.Atom "types";
          Sexp.List
            ( List.map letrec_types ~f:(fun (v, ty) ->
                  Sexp.List [Var.sexp_of_t v; Type.sexp_of_t ty]
                )
            )
        ];
        Sexp.List [
          Sexp.Atom "values";
          Sexp.List
            ( List.map letrec_vals ~f:(fun (var, value) ->
                  Sexp.List [Var.sexp_of_t var; sexp_of_t value]
                )
            )
        ];
        sexp_of_t letrec_body;
      ]
  | Const {const_val = c} ->
      Const.sexp_of_t c
and sexp_of_branch =
  let and_def cases def =
    match def with
    | None -> cases
    | Some lf -> Sexp.List [cases; sexp_of_leaf lf]
  in
  function
  | BLabel {lm_cases; lm_default} ->
      and_def
        (Map.sexp_of_m__t (module Label) sexp_of_branch lm_cases)
        lm_default
  | BConst {cm_cases; cm_default} ->
      and_def
        (Map.sexp_of_m__t (module Const) sexp_of_t cm_cases)
        cm_default
  | BLeaf lf ->
      sexp_of_leaf lf
and sexp_of_leaf {lf_var; lf_body} =
  let v = match lf_var with
    | Some v -> Var.sexp_of_t v
    | None -> Sexp.Atom "_"
  in
  Sexp.List [v; sexp_of_t lf_body]

let leaf_apply_kid lf ~f =
  { lf with lf_body = f lf.lf_body }

let rec branch_apply_kids b ~f =
  match b with
  | BLeaf lf -> BLeaf (leaf_apply_kid lf ~f)
  | BLabel {lm_cases; lm_default} -> BLabel {
      lm_cases = Map.map lm_cases ~f:(branch_apply_kids ~f);
      lm_default = Option.map lm_default ~f:(leaf_apply_kid ~f);
    }
  | BConst {cm_cases; cm_default} -> BConst {
      cm_cases = Map.map cm_cases ~f;
      cm_default = Option.map cm_default ~f:(leaf_apply_kid ~f);
    }

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
  | Match b -> Match (branch_apply_kids b ~f)
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
  | WithType{wt_expr; wt_type} ->
      WithType {
        wt_expr = f wt_expr;
        wt_type;
      }
  | Var _
  | EmptyRecord
  | GetField _
  | UpdateVal _
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
  | Match b -> Match (map_branch b ~f)
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
and map_branch b ~f = match b with
  | BLeaf lf -> BLeaf (map_leaf lf ~f)
  | BLabel {lm_cases; lm_default} -> BLabel {
      lm_cases = Map.map lm_cases ~f:(map_branch ~f);
      lm_default = Option.map lm_default ~f:(map_leaf ~f);
    }
  | BConst {cm_cases; cm_default} -> BConst {
      cm_cases = Map.map cm_cases ~f:(map ~f);
      cm_default = Option.map cm_default ~f:(map_leaf ~f);
    }
and map_leaf lf ~f = {lf with lf_body = map lf.lf_body ~f }

let rec subst: 'a t VarMap.t -> 'a t -> 'a t = fun env expr ->
  match expr with
  (* TODO: do stuff with type variables *)
  | Var {v_var = v; _} ->
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
  | Match b -> Match (subst_branch env b)
  | Let{let_v; let_e; let_body} ->
      Let {
        let_v;
        let_e = subst env let_e;
        let_body = subst (Map.remove env let_v) let_body;
      }
  | LetRec _ ->
      MuleErr.bug "TODO"
  | UpdateType{ut_lbl; ut_type; ut_record} ->
      UpdateType{
        ut_lbl;
        ut_type;
        ut_record = subst env ut_record;
      }
  | WithType {wt_expr; wt_type} ->
      WithType {
        wt_expr = subst env wt_expr;
        wt_type;
      }
  | Const _ | EmptyRecord | GetField _ | UpdateVal _ | Embed _ ->
      expr
and subst_branch env b = match b with
  | BLeaf lf -> BLeaf (subst_leaf env lf)
  | BLabel {lm_cases; lm_default} -> BLabel {
      lm_cases = Map.map lm_cases ~f:(subst_branch env);
      lm_default = Option.map lm_default ~f:(subst_leaf env);
    }
  | BConst {cm_cases; cm_default} -> BConst {
      cm_cases = Map.map cm_cases ~f:(subst env);
      cm_default = Option.map cm_default ~f:(subst_leaf env);
    }
and subst_leaf env lf =
  match lf.lf_var with
  | None -> leaf_apply_kid lf ~f:(subst env)
  | Some v -> leaf_apply_kid lf ~f:(subst (Map.remove env v))
