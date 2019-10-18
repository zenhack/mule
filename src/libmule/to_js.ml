open Common_ast

module Js = Js_pre
module D = Desugared_ast

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
  let name = Gensym.anon_var () in
  (name, Map.set env ~key:v ~data:(`Var name))

let add_lazy_var env v =
  let name = Gensym.anon_var () in
  (name, Map.set env ~key:v ~data:(`LazyVar name))

let translate_expr expr =
  let rec go env = function
    | D.Expr.Embed {e_value; _} ->
        Js.Const (Const.Text e_value)
    | D.Expr.Var {v_var} ->
        translate_var env v_var
    | D.Expr.Lam{l_param; l_body} ->
        let (param, env') = add_var env l_param in
        Js.Lam1(param, go env' l_body)
    | D.Expr.UpdateType{ut_record; _} -> go env ut_record
    | D.Expr.App {app_fn; app_arg} ->
        Js.Call1(go env app_fn, go env app_arg)
    | D.Expr.EmptyRecord ->
        Js.Object []
    | D.Expr.GetField{gf_lbl} ->
        Js.Lam1
          ( Var.of_string "o"
          , Js.Index
              ( Js.Var (Var.of_string "o")
              , Js.Const (Const.Text (Label.to_string gf_lbl))
              )
          )
    | D.Expr.Ctor{c_lbl; c_arg} ->
        Js.Tagged (c_lbl, go env c_arg)
    | D.Expr.ConstMatch {cm_cases; cm_default} ->
        Js.Lam1
          ( Var.of_string "v"
          , Js.Switch
              ( Js.Var (Var.of_string "v")
              , Map.to_alist cm_cases
                  |> List.map ~f:(fun (c, body) -> (c, go env body))
              , Some
                  (Js.Call1
                      ( go env cm_default
                      , Js.Var (Var.of_string "v")
                      )
                  );
              )
          )
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
    | D.Expr.UpdateVal {uv_lbl} ->
        Js.Lam1
          ( Var.of_string "r"
          , Js.Lam1
             ( Var.of_string "v"
             , Js.Update
                ( Js.Var (Var.of_string "r")
                , uv_lbl
                , Js.Var (Var.of_string "v")
                )
             )
          )
    | D.Expr.Match {cases; default} ->
        Js.Lam1
          ( Var.of_string "p"
          , Js.Switch
              ( Js.GetTag (Js.Var (Var.of_string "p"))
              , Map.to_alist cases
                  |> List.map ~f:(fun (lbl, (v, body)) ->
                      ( Const.Text (Label.to_string lbl)
                      , let (name, env') = add_var env v in
                          Js.Let
                            ( name
                            , Js.GetTagArg (Js.Var (Var.of_string "p"))
                            , go env' body
                            )
                      )
                    )
              , Option.map default ~f:(fun (v, body) ->
                    match v with
                    | None -> go env body
                    | Some v ->
                        let (name, env') = add_var env v in
                        Js.Let
                          ( name
                          , Js.Var (Var.of_string "p")
                          , go env' body
                          )
                  )
              )
          )
    | D.Expr.LetRec {letrec_vals; letrec_body; _} ->
        let env' =
          List.fold letrec_vals ~init:env ~f:(fun env (v, _) ->
              snd (add_lazy_var env v)
            )
        in
        let decls =
          List.map letrec_vals ~f:(fun (v, body) ->
            fun b ->
              Js.Let
                ( get_var env' v
                , Js.Lazy (go env' body)
                , b
                )
            )
        in
        let env'' =
          List.fold letrec_vals ~init:env ~f:(fun env (v, _) ->
              snd (add_var env v)
            )
        in
        let redecls =
          List.map letrec_vals ~f:(fun (v, _) ->
            fun b ->
              Js.Let
                ( get_var env'' v
                , translate_var env' v
                , b
                )
            )
        in
        List.fold_right
          (decls @ redecls)
          ~init:(go env'' letrec_body)
          ~f:(fun f body -> f body)
  in
  go VarMap.empty expr
