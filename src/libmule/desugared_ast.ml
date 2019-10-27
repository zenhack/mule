module Kind = Desugared_ast_kind
module Type = Desugared_ast_type
module Expr = Desugared_ast_expr

module SubstRec = struct
  open Common_ast

  type args = {
    rec_name: Var.t;
    type_vars: VarSet.t;
    val_vars: VarSet.t;
  }

  let mask_val args var =
    { args with val_vars = Set.remove args.val_vars var }

  let mask_type args var =
    { args with type_vars = Set.remove args.type_vars var }


  let rec typ: args -> 'i Type.t -> 'i Type.t = fun args ty -> match ty with
    | Type.Fn{fn_info; fn_pvar; fn_param; fn_ret} ->
        let args =
          match fn_pvar with
          | None -> args
          | Some v -> mask_val args v
        in
        Type.Fn {
          fn_info;
          fn_pvar;
          fn_param = typ args fn_param;
          fn_ret = typ args fn_ret;
        }
    | Type.Recur{mu_info; mu_var; mu_body} ->
        Type.Recur {
          mu_info;
          mu_var;
          mu_body = typ (mask_type args mu_var) mu_body;
        }
    | Type.Var {v_info; v_var} when Set.mem args.type_vars v_var ->
        Type.Path {
          p_info = v_info;
          p_var = args.rec_name;
          p_lbls = [var_to_label v_var];
        }
    | Type.Path{p_info; p_var; p_lbls} when Set.mem args.val_vars p_var ->
        Type.Path {
          p_info;
          p_var = args.rec_name;
          p_lbls = var_to_label p_var :: p_lbls;
        }
    | Type.Record {r_info; r_types; r_values; r_src} ->
        Type.Record {
          r_info;
          r_types = row args r_types;
          r_values = row args r_values;
          r_src;
        }
    | Type.Union {u_row} -> Type.Union{u_row = row args u_row}
    | Type.Quant {q_info; q_quant; q_var; q_body} ->
        Type.Quant {
          q_info;
          q_quant;
          q_var;
          q_body = typ (mask_type args q_var) q_body;
        }
    | Type.TypeLam {tl_info; tl_param; tl_body} ->
        Type.TypeLam {
          tl_info;
          tl_param;
          tl_body = typ (mask_type args tl_param) tl_body;
        }
    | Type.App{app_info; app_fn; app_arg} ->
        Type.App{
          app_info;
          app_fn = typ args app_fn;
          app_arg = typ args app_arg;
        }
    | Type.Var _
    | Type.Path _
    | Type.Named _
    | Type.Opaque _ -> ty
  and row: args -> 'i Type.row -> 'i Type.row =
    fun args {row_info; row_fields; row_rest} ->
    { row_info
    ; row_fields = List.map row_fields ~f:(fun (l, t) -> (l, typ args t))
    ; row_rest
      (* FIXME: we should potentially do a substitution here, but it's
       * not clear how since rest is [Var.t option], so we can't put another
       * expr there. *)
    }
  and expr: args -> 'i Expr.t -> 'i Expr.t = fun args e -> match e with
    | Expr.Var {v_var} when Set.mem args.val_vars v_var ->
        Expr.App {
          app_fn = Expr.GetField{gf_lbl = var_to_label v_var};
          app_arg = Expr.Var{v_var = args.rec_name};
        }
    | Expr.Lam{l_param; l_body} ->
        Expr.Lam {
          l_param;
          l_body = expr (mask_val args l_param) l_body;
        }
    | Expr.Let{let_v; let_e; let_body} ->
        Expr.Let{
          let_v;
          let_e = expr args let_e;
          let_body = expr (mask_val args let_v) let_body;
        }
    | Expr.WithType {wt_expr; wt_type} ->
        Expr.WithType {
          wt_expr = expr args wt_expr;
          wt_type = typ args wt_type;
        }
    | Expr.Ctor {c_lbl; c_arg} ->
        Expr.Ctor{c_lbl; c_arg = expr args c_arg}
    | Expr.App{app_fn; app_arg} ->
        Expr.App {
          app_fn = expr args app_fn;
          app_arg = expr args app_arg;
        }
    | Expr.Match{cases; default} ->
        Expr.Match {
          cases = Map.map cases ~f:(fun (v, e) ->
              (v, expr (mask_val args v) e)
            );
          default =
            Option.map default ~f:(function
              | (None, body) -> (None, expr args body)
              | (Some v, body) -> (Some v, expr (mask_val args v) body)
            )
        }
    | Expr.ConstMatch{cm_cases; cm_default} ->
        Expr.ConstMatch {
          cm_cases = Map.map cm_cases ~f:(expr args);
          cm_default = expr args cm_default;
        }
    | Expr.LetRec{letrec_vals; letrec_types; letrec_body} ->
        let remove_batch set vars =
          List.fold vars ~init:set ~f:(fun acc (k, _) -> Set.remove acc k)
        in
        let args =
          { args with
            type_vars = remove_batch args.type_vars letrec_types;
            val_vars = remove_batch args.val_vars letrec_vals;
          }
        in
        Expr.LetRec {
          letrec_types = List.map letrec_types ~f:(fun (k, v) -> (k, typ args v));
          letrec_vals = List.map letrec_vals ~f:(fun (k, v) -> (k, expr args v));
          letrec_body = expr args letrec_body;
        }
    | Expr.UpdateType{ut_lbl; ut_type; ut_record} ->
        Expr.UpdateType {
          ut_lbl;
          ut_type = typ args ut_type;
          ut_record = expr args ut_record;
        }
    | Expr.Var _
    | Expr.EmptyRecord
    | Expr.GetField _
    | Expr.UpdateVal _
    | Expr.Embed _
    | Expr.Const _ -> e
end
