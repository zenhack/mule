open Common_ast

module Js = Js_ast
module D = Desugared_ast

let translate_const = function
  | Const.Integer n -> Js.BigInt n
  | Const.Text s -> Js.String s
  | Const.Char c -> Js.String (String.make 1 c)

let force e =
  Js.Call(Js.Var "$force", [e])

let translate_var env v =
  match Util.find_exn env v with
  | `Var var -> Js.Var(Var.to_string var)
  | `LazyVar var ->
      force (Js.Var (Var.to_string var))

let get_var_name env v =
  match Util.find_exn env v with
  | `Var var -> Var.to_string var
  | `LazyVar var -> Var.to_string var

let add_var env v =
  let name = Gensym.anon_var () in
  (Var.to_string name, Map.set env ~key:v ~data:(`Var name))

let add_lazy_var env v =
  let name = Gensym.anon_var () in
  (Var.to_string name, Map.set env ~key:v ~data:(`LazyVar name))

let translate_expr expr =
  let rec go env = function
    | D.Expr.Embed {e_value; _} ->
        Js.String e_value
    | D.Expr.Var {v_var} ->
        translate_var env v_var
    | D.Expr.Lam{l_param; l_body} ->
        let (param, env') = add_var env l_param in
        Js.Lam([param], `E (go env' l_body))
    | D.Expr.App {app_fn; app_arg} ->
        begin match app_fn with
          | D.Expr.WithType _ ->
              go env app_arg
          | D.Expr.App {app_fn = D.Expr.Update {up_level = `Type; _}; app_arg = ret} ->
              go env ret
          | _ ->
              Js.Call(go env app_fn, [go env app_arg])
        end
    | D.Expr.EmptyRecord ->
        Js.Object []
    | D.Expr.GetField{gf_lbl} ->
        Js.Lam(["o"], `E (Js.Index(Js.Var "o", Js.String (Label.to_string gf_lbl))))
    | D.Expr.Ctor{c_lbl; c_arg} ->
        Js.Array [
          Js.String (Label.to_string c_lbl);
          go env c_arg;
        ]
    | D.Expr.ConstMatch {cm_cases; cm_default} ->
        Js.Lam
          ( ["v"]
          , `S [
              Js.Switch {
                sw_scrutinee = Js.Var "v";
                sw_default =
                  Some [Js.Return (Js.Call (go env cm_default, [Js.Var "v"]))];
                sw_cases =
                  Map.to_alist cm_cases
                  |> List.map ~f:(fun (c, body) ->
                      ( translate_const c
                      , [Js.Return (go env body)]
                      )
                    )
              }
            ]
          )
    | D.Expr.Let {let_v; let_e; let_body} ->
        let (name, env') = add_var env let_v in
        Js.Call
          ( Js.Lam([name], `E (go env' let_body))
          , [go env let_e]
          )
    | D.Expr.Const {const_val} ->
        translate_const const_val
    | D.Expr.WithType _ -> Js.Lam(["x"], `E (Js.Var "x"))
    | D.Expr.Witness _ -> Js.Null
    | D.Expr.Update {up_level = `Type; _} ->
        Js.Lam(["x"], `E (Js.Lam(["y"], `E (Js.Var "x"))))
    | D.Expr.Update {up_level = `Value; up_lbl} ->
        Js.Lam
          ( ["r"]
          , `E ( Js.Lam
                   ( ["v"]
                   , `E
                       (Js.Call
                          ( Js.Var "$update"
                          , [
                            Js.Var "r";
                            Js.String (Label.to_string up_lbl);
                            Js.Var "v";
                          ]
                          )
                       )
                   ))
          )
    | D.Expr.Match {cases; default} ->
        Js.Lam
          ( ["p"]
          , `S [
              Js.Switch {
                sw_scrutinee = Js.Index (Js.Var "p", Js.Int 0);
                sw_cases =
                  Map.to_alist cases
                  |> List.map ~f:(fun (lbl, (v, body)) ->
                      ( Js.String (Label.to_string lbl)
                      , let (name, env') = add_var env v in [
                          Js.VarDecl
                            ( name
                            , Js.Index (Js.Var "p", Js.Int 1)
                            );
                          Js.Return (go env' body);
                        ]
                      )
                    );
                sw_default = Option.map default ~f:(fun (v, body) ->
                    match v with
                    | None -> [Js.Return (go env body)]
                    | Some v ->
                        let (name, env') = add_var env v in [
                          Js.VarDecl(name, Js.Var "p");
                          Js.Return(go env' body);
                        ]

                  )
              };
            ]
          )
    | D.Expr.LetRec {letrec_vals; letrec_body; _} ->
        let env' =
          List.fold letrec_vals ~init:env ~f:(fun env (v, _) ->
              snd (add_lazy_var env v)
            )
        in
        let decls =
          List.map letrec_vals ~f:(fun (v, body) ->
              Js.VarDecl
                ( get_var_name env' v
                , Js.Call(Js.Var "$lazy", [Js.Lam ([], `E (go env' body))])
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
              Js.VarDecl(get_var_name env'' v, translate_var env' v)
            )
        in
        Js.Call
          ( Js.Lam
              ( []
              , `S (decls @ redecls @ [Js.Return (go env'' letrec_body)])
              )
          , []
          )
  in
  go VarMap.empty expr
