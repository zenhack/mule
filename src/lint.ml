open Ast.Surface
open Ast.Surface.Expr

let err e =
  raise (MuleErr.MuleExn e)
let duplicate_fields dups =
  err (MuleErr.DuplicateFields dups)

(* Check for duplicate record fields (in both expressions and types) *)
let check_duplicate_record_fields =
  let rec go_expr = function
    | Import _ | Embed _ | Const _ -> ()
    | Record fields ->
        go_fields fields
    | Update(e, fields) ->
        go_expr e; go_fields fields

    | Lam (pats, body) ->
        List.iter pats ~f:go_pat;
        go_expr body
    | Match(e, cases) ->
        go_expr e;
        List.iter cases ~f:go_case
    | App (f, x) -> go_expr f; go_expr x
    | GetField(e, _) -> go_expr e
    | Let(bindings, body) ->
        go_let bindings;
        go_expr body
    | Var _ -> ()
    | Ctor _ -> ()
    | WithType(e, ty) ->
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
    | Pattern.Ctor(_, pat) -> go_pat pat
    | Pattern.Var (_, None) | Pattern.Wild -> ()
    | Pattern.Var (_, Some ty) -> go_type ty
  and go_type = function
    | Type.Import _
    | Type.Var _
    | Type.Path _
    | Type.Ctor _
    | Type.RowRest _ -> ()
    | Type.Quant(_, _, ty) -> go_type ty
    | Type.Recur(_, ty) -> go_type ty
    | Type.Fn(param, ret) -> go_type param; go_type ret
    | Type.Record fields ->
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
    | Type.Union(l, r) -> go_type l; go_type r
    | Type.App(f, x) -> go_type f; go_type x
    | Type.Annotated(_, ty) -> go_type ty
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
