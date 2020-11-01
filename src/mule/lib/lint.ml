open Common_ast
open Surface_ast
open Surface_ast.Expr

module Dup_fields = struct
  let duplicate_fields level dups =
    MuleErr.throw (`DuplicateFields (level, dups))

  let rec go_expr Loc.{l_value; _} = match l_value with
    | Import _ | Embed _ | Const _ -> ()
    | Record {r_fields = fields; _} ->
        go_fields fields
    | Update{up_arg = e; up_fields = fields; _} ->
        go_expr e; go_fields fields
    | List{l_elts} ->
        List.iter l_elts ~f:go_expr
    | Lam {lam_params = pats; lam_body = body; _} ->
        List.iter pats ~f:go_pat;
        go_expr body
    | Match{match_arg = e; match_cases = cases; _} ->
        go_expr e;
        List.iter cases ~f:go_case
    | App {app_fn = f; app_arg = x; _} -> go_expr f; go_expr x
    | GetField{gf_arg = e; _} -> go_expr e
    | Let{let_binds = bindings; let_body = body; _} ->
        go_let bindings;
        go_expr body
    | Var _ -> ()
    | Ctor _ -> ()
    | WithType{wt_term = e; wt_type = ty; _} ->
        go_expr e;
        go_type ty
    | Quote e | Unquote e | UnquoteSplice e ->
        go_expr e
  and go_let =
    List.iter ~f:(fun Loc.{l_value; _} -> match l_value with
      | `BindVal(pat, e) ->
          go_pat pat;
          go_expr e
      | `BindType(_, _, ty) -> go_type ty
    )
  and go_fields fields =
    List.iter fields ~f:(fun Loc.{l_value; _} -> match l_value with
      | `Value (_, ty, e) ->
          Option.iter ty ~f:go_type;
          go_expr e
      | `Type (_, _, ty) ->
          go_type ty
    );
    let (val_lbls, type_lbls) =
      List.partition_map fields ~f:(fun Loc.{l_value; _} -> match l_value with
        | `Value (lbl, _, _) -> First lbl
        | `Type (lbl, _, _) -> Second lbl
      )
    in
    go_labels `Value val_lbls;
    go_labels `Type type_lbls
  and go_pat Loc.{l_value; _} = match l_value with
    | Pattern.Const _ -> ()
    | Pattern.Ctor{c_arg; _} -> go_pat c_arg
    | Pattern.Var {v_type = None; _} | Pattern.Wild -> ()
    | Pattern.Var {v_type = Some ty; _} -> go_type ty
  and go_type Loc.{l_value; _} = match l_value with
    | Type.Import _
    | Type.Var _
    | Type.Path _
    | Type.Ctor _
    | Type.RowRest _ -> ()
    | Type.Quant{q_body; _} -> go_type q_body
    | Type.Recur{recur_body = ty; _} -> go_type ty
    | Type.Fn{fn_param; fn_ret; _} -> go_type fn_param; go_type fn_ret
    | Type.Record {r_items = fields; _} ->
        let (val_lbls, type_lbls, _) =
          List.partition3_map fields ~f:(fun loc_lbl -> match loc_lbl.Loc.l_value with
            | Type.Rest _ -> `Trd ()
            | Type.Field(lbl, ty) ->
                go_type ty;
                `Fst lbl
            | Type.Type(lbl, _, Some ty) ->
                go_type ty;
                `Snd lbl
            | Type.Type (lbl, _, None) ->
                `Snd lbl
          )
        in
        go_labels `Value val_lbls;
        go_labels `Type type_lbls
    | Type.Union{u_l = l; u_r = r; _} -> go_type l; go_type r
    | Type.App{app_fn = f; app_arg = x; _} -> go_type f; go_type x
    | Type.Annotated{anno_ty; _} ->
        go_type anno_ty
  and go_labels: [`Type|`Value] -> Label.t Loc.located list -> unit =
    fun level lst ->
    let map =
      List.fold
        lst
        ~init:(Map.empty (module Label))
        ~f:(fun map {l_value; l_loc} ->
          Map.update map l_value ~f:(function
            | None -> [l_loc]
            | Some locs -> (l_loc :: locs)
          )
        )
    in
    let dups = Map.filter map ~f:(function
        | [] | [_] -> false
        | _ -> true
      )
    in
    begin match Map.to_alist dups with
      | [] -> ()
      | dups_list -> duplicate_fields level dups_list
    end
  and go_case (pat, body) =
    go_pat pat;
    go_expr body
end

(* TODO: check for duplicate bound variables (in recursive lets). *)
let check_expr = Dup_fields.go_expr
let check_type = Dup_fields.go_type
