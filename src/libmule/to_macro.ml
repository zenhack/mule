
include To_macro_t

module Const = Common_ast.Const
module S = Surface_ast
module M = Macro_ast
module Wm = With_meta

let unbound_var v = M.{
  v_id = 0;
  v_name = Common_ast.Var.to_string v;
}

let wrap_meta meta data = Wm.{meta; data}

let wrap_exp  s m = wrap_meta (SurfaceExpr    s) m
let wrap_pat  s m = wrap_meta (SurfacePattern s) m
let wrap_type s m = wrap_meta (SurfaceType    s) m

let rec expr ctx e = match e with
  | S.Expr.Var {v_var} ->
      wrap_exp e (M.EVar (unbound_var v_var))
  | S.Expr.App {app_fn; app_arg} ->
      wrap_exp e (M.EApp(expr ctx app_fn, expr ctx app_arg))
  | S.Expr.Lam{lam_params; lam_body} ->
      List.fold_right
        lam_params
        ~init:(expr ctx lam_body)
        ~f:(fun p body -> Wm.{
            data = M.ELam(pattern p, body);
            meta = SurfaceExpr e; (* TODO: more precise *)
          })
  | S.Expr.Embed{e_path; _} ->
      wrap_exp e (M.EConst (Const.Text (ctx.resolve_embed_exn e_path)))
and pattern p = match p with
  | S.Pattern.Var {v_var; v_type = None} ->
      wrap_pat p (M.PVar (unbound_var v_var))
and typ t =
  match t with
  | S.Type.Fn {fn_param; fn_ret} ->
      wrap_type t (M.TFn (typ fn_param, typ fn_ret))
  | S.Type.Var {v_var} ->
      wrap_type t (M.TVar (unbound_var v_var))

let expr_exn = expr
let typ_exn _ = typ
