open Surface_ast
open Surface_ast.Expr

let duplicate_fields dups =
  MuleErr.throw (`DuplicateFields dups)

(* Check for duplicate record fields (in both expressions and types) *)
let check_duplicate_record_fields =
  let rec go_expr = function
    | Import _ | Embed _ | Const _ -> ()
    | Record {r_fields = fields} ->
        go_fields fields
    | Update{up_arg = e; up_fields = fields} ->
        go_expr e; go_fields fields

    | Lam {lam_params = pats; lam_body = body} ->
        List.iter pats ~f:go_pat;
        go_expr body
    | Match{match_arg = e; match_cases = cases} ->
        go_expr e;
        List.iter cases ~f:go_case
    | App {app_fn = f; app_arg = x} -> go_expr f; go_expr x
    | GetField{gf_arg = e; _} -> go_expr e
    | Let{let_binds = bindings; let_body = body} ->
        go_let bindings;
        go_expr body
    | Var _ -> ()
    | Ctor _ -> ()
    | WithType{wt_term = e; wt_type = ty} ->
        go_expr e;
        go_type ty
  and go_let =
    List.iter ~f:(function
      | `BindVal(pat, e) ->
          go_pat pat;
          go_expr e
      | `BindType(_, _, ty) -> go_type ty
    )
  and go_fields fields =
    List.iter fields ~f:(function
      | `Value (_, ty, e) ->
          Option.iter ty ~f:go_type;
          go_expr e
      | `Type (_, _, ty) ->
          go_type ty
    );
    let labels = List.map fields ~f:(function
        | `Value (lbl, _, _) -> lbl
        | `Type (lbl, _, _) -> lbl
      ) in
    go_labels labels
  and go_pat = function
    | Pattern.Const _ -> ()
    | Pattern.Ctor{c_arg; _} -> go_pat c_arg
    | Pattern.Var {v_type = None; _} | Pattern.Wild -> ()
    | Pattern.Var {v_type = Some ty; _} -> go_type ty
  and go_type = function
    | Type.Import _
    | Type.Var _
    | Type.Path _
    | Type.Ctor _
    | Type.RowRest _ -> ()
    | Type.Quant{q_body; _} -> go_type q_body
    | Type.Recur{recur_body = ty; _} -> go_type ty
    | Type.Fn{fn_param; fn_ret} -> go_type fn_param; go_type fn_ret
    | Type.Record {r_items = fields} ->
        List.map fields ~f:(function
          | Type.Rest _ -> []
          | Type.Field(lbl, ty)
          | Type.Type(lbl, _, Some ty) ->
              go_type ty;
              [lbl]
          | Type.Type (lbl, _, None) ->
              [lbl]
        )
        |> List.concat
        |> go_labels
    | Type.Union{u_l = l; u_r = r} -> go_type l; go_type r
    | Type.App{app_fn = f; app_arg = x} -> go_type f; go_type x
    | Type.Annotated{anno_ty; anno_var = _} ->
        go_type anno_ty
  and go_labels =
    let rec go all dups = function
      | (l :: ls) when Set.mem all l ->
          go all (Set.add dups l) ls
      | (l :: ls) ->
          go (Set.add all l) dups ls
      | [] when Set.is_empty dups -> ()
      | [] -> duplicate_fields (Set.to_list dups)
    in go LabelSet.empty LabelSet.empty
  and go_case (pat, body) =
    go_pat pat;
    go_expr body
  in
  go_expr

let check expr =
  check_duplicate_record_fields expr
(* TODO: check for duplicate bound variables (in recursive lets). *)
