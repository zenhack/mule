include Desugared_ast_expr_t
open Common_ast
module Type = Desugared_ast_type

let rec sexp_of_t = function
  | Embed { e_path; _ } ->
      Sexp.List [Sexp.Atom "embed"; Sexp.Atom e_path]
  | Import { i_orig_path; i_resolved_path; _} ->
      Sexp.List [
        Sexp.Atom "import";
        String.sexp_of_t i_orig_path;
        Paths.sexp_of_t i_resolved_path;
      ]
  | Var { v_var = v; _ } -> Sexp.Atom (Var.to_string v)
  | Lam{ l_param = v; l_body = body } ->
      Sexp.List [Sexp.Atom "fn"; Var.sexp_of_t v; sexp_of_t body]
  | App{app_fn; app_arg} ->
      Sexp.List [sexp_of_t app_fn; sexp_of_t app_arg]
  | Record r ->
      Sexp.List (Sexp.Atom "record" :: sexps_of_rec_bind r)
  | GetField{gf_lbl; gf_record} -> Sexp.List [
      Sexp.Atom ".";
      sexp_of_t gf_record;
      Label.sexp_of_t gf_lbl;
    ]
  | UpdateVal {uv_lbl; uv_val; uv_record} -> Sexp.List [
      Sexp.Atom ".=";
      Label.sexp_of_t uv_lbl;
      sexp_of_t uv_val;
      sexp_of_t uv_record;
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
  | WithType {wt_expr = e; wt_type = ty; _} ->
      Sexp.List [Sexp.Atom ":"; sexp_of_t e; Type.sexp_of_t ty]
  | Let{let_v = v; let_e = e; let_body = body} ->
      Sexp.List [
        Sexp.Atom "let";
        Sexp.List [Var.sexp_of_t v; sexp_of_t e];
        sexp_of_t body;
      ]
  | LetRec{letrec_binds; letrec_body} ->
      Sexp.List (
        [Sexp.Atom "letrec"]
        @ sexps_of_rec_bind letrec_binds
        @ [sexp_of_t letrec_body]
      )
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
and sexps_of_rec_bind {rec_types; rec_vals} = [
  Sexp.List [
    Sexp.Atom "types";
    Sexp.List
      (List.map rec_types ~f:(fun ts ->
            (List.map ts ~f:(fun (v, ty) ->
                  Sexp.List [Var.sexp_of_t v; Type.sexp_of_t ty]
                )
             |> fun l -> Sexp.List l)))
  ];
  Sexp.List [
    Sexp.Atom "values";
    Sexp.List
      ( List.map rec_vals ~f:(fun (var, value) ->
            Sexp.List [Var.sexp_of_t var; sexp_of_t value]
          )
      )
  ];
]

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

let rec apply_to_kids e ~f = match e with
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
  | LetRec{letrec_binds; letrec_body} ->
      LetRec {
        letrec_binds = apply_to_rec_kids letrec_binds ~f;
        letrec_body = f letrec_body;
      }
  | Record r ->
      Record (apply_to_rec_kids r ~f)
  | UpdateType{ut_lbl; ut_type; ut_record} ->
      UpdateType {
        ut_lbl;
        ut_type;
        ut_record = f ut_record;
      }
  | WithType{wt_src; wt_expr; wt_type} ->
      WithType {
        wt_src;
        wt_expr = f wt_expr;
        wt_type;
      }
  | GetField {gf_lbl; gf_record} ->
      GetField {
        gf_lbl;
        gf_record = f gf_record;
      }
  | UpdateVal {uv_lbl; uv_record; uv_val} ->
      UpdateVal {
        uv_lbl;
        uv_record = f uv_record;
        uv_val = f uv_val;
      }
  | Var _
  | Embed _
  | Import _
  | Const _ -> e
and apply_to_rec_kids {rec_types; rec_vals} ~f = {
  rec_types;
  rec_vals = List.map rec_vals ~f:(fun (v, e) -> (v, f e));
}
let rec map e ~f =
  match e with
  | WithType {wt_src; wt_expr = e; wt_type = ty} ->
      WithType {
        wt_src;
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
  | LetRec{letrec_binds; letrec_body} ->
      LetRec {
        letrec_binds = map_rec_bind letrec_binds ~f;
        letrec_body = map letrec_body ~f;
      }
  | Record r ->
      Record (map_rec_bind r ~f)
  | UpdateType{ut_lbl; ut_type; ut_record} ->
      UpdateType {
        ut_lbl;
        ut_type = Type.map ut_type ~f;
        ut_record = map ut_record ~f;
      }
  | GetField {gf_lbl; gf_record} ->
      GetField {
        gf_lbl;
        gf_record = map gf_record ~f;
      }
  | UpdateVal{uv_lbl; uv_val; uv_record} ->
      UpdateVal {
        uv_lbl;
        uv_val = map uv_val ~f;
        uv_record = map uv_record ~f;
      }
  | Var x -> Var x
  | Const x -> Const x
  | Embed x -> Embed x
  | Import x -> Import x
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
and map_rec_bind {rec_types; rec_vals} ~f = {
  rec_types = List.map rec_types ~f:(List.map ~f:(fun (v, ty) -> (v, Type.map ty ~f)));
  rec_vals = List.map rec_vals ~f:(fun (v, e) -> (v, map e ~f));
};
