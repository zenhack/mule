include Desugared_ast_expr_t
open Common_ast
module Type = Desugared_ast_type

let rec fv: 'a t -> VarSet.t = function
  (* Find all free variables in the expression. *)
  | Embed _ | Import _ | Const _ | WithType _ ->
      Set.empty (module Var)
  | Var {v_var; _} ->
      Set.singleton (module Var) v_var
  | Lam {l_param; l_body; _} ->
      Set.remove (fv l_body) l_param
  | App {app_fn; app_arg} ->
      Set.union (fv app_fn) (fv app_arg)
  | Record _ ->
      failwith "TODO: fv(record)"
  | GetField {gf_record; _} ->
      fv gf_record
  | UpdateType {ut_record; _} ->
      fv ut_record
  | UpdateVal {uv_record; _} ->
      fv uv_record
  | Match {m_branch; _} -> fv_branch m_branch
  | Ctor {c_arg; _} ->
      fv c_arg
  | Let {let_v; let_e; let_body} ->
      Set.union (fv let_e) (Set.remove (fv let_body) let_v)
  | LetType{lettype_body; _} ->
      fv lettype_body
  | LetRec _ ->
      failwith "TODO: fv(letrec)"
and fv_branch = function
  | BLabel {lm_cases; lm_default} ->
      Map.fold
        lm_cases
        ~init:(fv_branchdef lm_default)
        ~f:(fun ~key:_ ~data vs -> Set.union (fv_branch data) vs)
  | BConst {cm_cases; cm_default} ->
      Map.fold
        cm_cases
        ~init:(fv_branchdef cm_default)
        ~f:(fun ~key:_ ~data vs -> Set.union (fv data) vs)
  | BLeaf l ->
      fv_leaf l
and fv_branchdef = function
  | None -> Set.empty (module Var)
  | Some l -> fv_leaf l
and fv_leaf {lf_var; lf_body} = match lf_var with
  | Some v -> Set.remove (fv lf_body) v
  | None -> fv lf_body


let get_src_expr: 'a t -> Surface_ast.Expr.lt option = function
  | Var {v_src = `Sourced v; _} ->
      Some Loc.{
          l_value = Surface_ast.Expr.Var {v_var = v};
          l_loc = v.l_loc;
        }
  | WithType {wt_src = `WithType(e, ty); _} -> Some Loc.{
      l_loc = spanning e.l_loc ty.l_loc;
      l_value = Surface_ast.Expr.WithType {
          wt_term = e;
          wt_type = ty;
        }
    }
  | Import {i_src = `SurfaceImport li; _} ->
      Some (Loc.map li ~f:(fun i -> Surface_ast.Expr.Import i))
  | Embed {e_src; _} ->
      Some e_src
  | _ ->
      None

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
  | Lam{ l_param = v; l_body = body; l_src = _ } ->
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
  | Match {m_branch; m_src = _} -> Sexp.List [
      Sexp.Atom "match";
      sexp_of_branch m_branch;
    ]
  | WithType {wt_type = ty; _} ->
      Sexp.List [Sexp.Atom ":"; Type.sexp_of_t ty]
  | Let{let_v = v; let_e = e; let_body = body} ->
      Sexp.List [
        Sexp.Atom "let";
        Sexp.List [Var.sexp_of_t v; sexp_of_t e];
        sexp_of_t body;
      ]
  | LetType{lettype_v = v; lettype_t = t; lettype_body = body} ->
      Sexp.List [
        Sexp.Atom "lettype";
        Sexp.List [Var.sexp_of_t v; Type.sexp_of_t t];
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
      (List.map rec_types ~f:(fun (v, ty) ->
        Sexp.List [Var.sexp_of_t v; Type.sexp_of_t ty]
      ));
  ];
  Sexp.List [
    Sexp.Atom "values";
    Sexp.List
      ( List.map rec_vals ~f:(fun (var, ty, value) ->
            match ty with
            | None -> Sexp.List [Var.sexp_of_t var; sexp_of_t value]
            | Some ty -> Sexp.List [
                Var.sexp_of_t var;
                Type.sexp_of_t ty;
                sexp_of_t value;
              ]
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
  | Lam {l_param; l_body; l_src} -> Lam {
      l_param;
      l_src;
      l_body = f l_body
    }
  | App{app_fn; app_arg} -> App {
      app_fn = f app_fn;
      app_arg = f app_arg;
    }
  | Ctor{c_lbl; c_arg} -> Ctor{c_lbl; c_arg = f c_arg}
  | Match {m_branch; m_src} -> Match {
      m_branch = branch_apply_kids m_branch ~f;
      m_src;
    }
  | Let{let_v; let_e; let_body} -> Let {
      let_v;
      let_e = f let_e;
      let_body = f let_body
    }
  | LetType{lettype_v; lettype_t; lettype_body} -> LetType {
      lettype_v;
      lettype_t;
      lettype_body = f lettype_body;
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
  | WithType{wt_src; wt_type} ->
      WithType {
        wt_src;
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
  rec_vals = List.map rec_vals ~f:(fun (v, ty, e) -> (v, ty, f e));
}
let rec map e ~f =
  match e with
  | WithType {wt_src; wt_type = ty} ->
      WithType {
        wt_src;
        wt_type = Type.map ty ~f;
      }
  | Lam{l_param; l_src; l_body} ->
      Lam{l_param; l_src; l_body = map l_body ~f}
  | App{app_fn; app_arg}-> App {
      app_fn = map app_fn ~f;
      app_arg = map app_arg ~f;
    }
  | Ctor{c_lbl; c_arg} -> Ctor{c_lbl; c_arg = map c_arg ~f}
  | Match {m_branch; m_src} -> Match {
      m_branch = map_branch m_branch ~f;
      m_src;
    }
  | Let{let_v; let_e; let_body} -> Let{
      let_v;
      let_e = map let_e ~f;
      let_body = map let_body ~f;
    }
  | LetType{lettype_v; lettype_t; lettype_body} -> LetType{
      lettype_v;
      lettype_t = Type.map lettype_t ~f;
      lettype_body = map lettype_body ~f;
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
  rec_types = List.map rec_types ~f:(fun (v, ty) -> (v, Type.map ty ~f));
  rec_vals = List.map rec_vals ~f:(fun (v, ty, e) ->
      ( v
      , Option.map ty ~f:(Type.map ~f)
      , map e ~f
      )
    );
};
