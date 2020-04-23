open Common_ast

module Js = Js_pre
module D = Desugared_ast

let intrinsics_env =
  ["int"; "text"; "char"]
  |> List.map ~f:(fun v ->
    let v = Var.of_string v in
    (v, `Var v)
  )
  |> Map.of_alist_exn (module Var)

let force e =
  Js.Call1(Js.Var (Var.of_string "$force"), e)

let translate_var env v =
  match Util.find_exn env v with
  | `Var var -> Js.Var var
  | `LazyVar var ->
      force (Js.Var var)

let get_var env v =
  match Util.find_exn env v with
  | `Var var -> var
  | `LazyVar var -> var

let add_var env v =
  let name = Gensym.anon_var Gensym.global in
  (name, Map.set env ~key:v ~data:(`Var name))

let add_lazy_var env v =
  let name = Gensym.anon_var Gensym.global in
  (name, Map.set env ~key:v ~data:(`LazyVar name))

let js_let (v, e, body) =
  Js.Call1(Js.Lam1(v, body), e)

let translate_expr ~get_import expr =
  let rec go env = function
    | D.Expr.Embed {e_value; _} ->
        Js.Const (Const.Text e_value)
    | D.Expr.Import {i_resolved_path; _} ->
        Js.Var (get_import i_resolved_path)
    | D.Expr.Var {v_var; _} ->
        translate_var env v_var
    | D.Expr.Lam{l_param; l_body; _} ->
        let (param, env') = add_var env l_param in
        Js.Lam1(param, go env' l_body)
    | D.Expr.UpdateType{ut_record; _} -> go env ut_record
    | D.Expr.App {app_fn; app_arg} ->
        Js.Call1(go env app_fn, go env app_arg)
    | D.Expr.GetField{gf_lbl; gf_record} ->
        Js.Index
          ( go env gf_record
          , Js.Const (Const.Text (Label.to_string gf_lbl))
          )
    | D.Expr.Ctor{c_lbl; c_arg} ->
        Js.Tagged (c_lbl, go env c_arg)
    | D.Expr.Let {let_v; let_e; let_body} ->
        let (name, env') = add_var env let_v in
        Js.Call1
          ( Js.Lam1(name, go env' let_body)
          , go env let_e
          )
    | D.Expr.Const {const_val} ->
        Js.Const const_val
    | D.Expr.WithType {wt_expr; _} ->
        go env wt_expr
    | D.Expr.UpdateVal {uv_lbl; uv_val; uv_record} ->
        Js.Update
          ( go env uv_record
          , uv_lbl
          , go env uv_val
          )
    | D.Expr.Match {m_branch; _} ->
        let v = Var.of_string "p" in
        let arg = Js.Var v in
        Js.Lam1
          ( v
          , begin match m_branch with
            | D.Expr.BLeaf lf ->
                go_leaf env lf arg
            | D.Expr.BConst {cm_cases; cm_default} ->
                Js.Switch (go_const_match env cm_cases cm_default arg)
            | D.Expr.BLabel {lm_cases; lm_default} ->
                Js.Switch (go_lbl_match env lm_cases lm_default arg)
          end
          )
    | D.Expr.LetRec {letrec_binds = {rec_vals; _}; letrec_body; _} ->
        go_letrec env rec_vals ~mkbody:(fun env -> go env letrec_body)
    | D.Expr.Record {rec_vals; _}->
        go_letrec
          env
          rec_vals
          ~mkbody:(fun env ->
            (Js.Object (List.map rec_vals ~f:(fun (v, _, _) ->
                  (var_to_label v, translate_var env v)))))
  and go_letrec env rec_vals ~mkbody =
    let env' =
      List.fold rec_vals ~init:env ~f:(fun env (v, _, _) ->
        snd (add_lazy_var env v)
      )
    in
    let binds =
      List.map rec_vals ~f:(fun (v, _, body) ->
        ( get_var env' v
        , Js.Lazy (go env' body)
        )
      )
    in
    let env'' =
      List.fold rec_vals ~init:env ~f:(fun env (v, _, _) ->
        snd (add_var env v)
      )
    in
    let body' =
      List.fold
        rec_vals
        ~init:(mkbody env'')
        ~f:(fun body (v, _, _) ->
          js_let
            ( get_var env'' v
            , translate_var env' v
            , body
            )
        )
    in
    Js.LetRec(binds, body')
  and go_branch env b arg =
    match b with
    | D.Expr.BLeaf lf -> Js.BLeaf (go_leaf env lf arg)
    | D.Expr.BLabel {lm_cases; lm_default} ->
        Js.BBranch (go_lbl_match env lm_cases lm_default arg)
    | D.Expr.BConst {cm_cases; cm_default} ->
        Js.BBranch (go_const_match env cm_cases cm_default arg)
  and go_lbl_match env lm_cases lm_default arg = {
    sw_arg = Js.GetTag arg;
    sw_cases =
      Map.to_alist lm_cases
      |> List.map ~f:(fun (lbl, b') ->
        ( Const.Text (Label.to_string lbl)
        , go_branch env b' (Js.GetTagArg arg)
        )
      );
    sw_default =
      Option.map lm_default ~f:(fun lf ->
        go_leaf env lf arg
      );
  }
  and go_const_match env cm_cases cm_default arg = {
    sw_arg = arg;
    sw_cases =
      Map.to_alist cm_cases
      |> List.map ~f:(fun (c, body) -> (c, Js.BLeaf (go env body)));
    sw_default =
      Option.map cm_default ~f:(fun lf -> go_leaf env lf arg);
  }
  and go_leaf env {lf_var; lf_body} arg =
    begin match lf_var with
      | None -> go env lf_body
      | Some v ->
          let (name, env') = add_var env v in
          js_let
            ( name
            , arg
            , go env' lf_body
            )
    end
  in
  go intrinsics_env expr
