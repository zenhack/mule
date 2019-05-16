module SP = Ast.Surface.Pattern
module S = Ast.Surface.Expr
module ST = Ast.Surface.Type
module D = Ast.Desugared.Expr
module DT = Ast.Desugared.Type
module DK = Ast.Desugared.Kind

let incomplete_pattern p =
  raise (MuleErr.MuleExn (MuleErr.IncompletePattern p))

let var_to_lbl v = Ast.Var.to_string v |> Ast.Label.of_string

let rec desugar_type = function
  | ST.Fn(param, ret) ->
      DT.Fn((), desugar_type param, desugar_type ret)
  | ST.Quant(q, vars, body) ->
      desugar_q_type q vars body
  | ST.Recur(v, body) ->
      DT.Recur((), v, desugar_type body)
  | ST.Var v ->
      DT.Var((), v)
  | ST.Union u ->
      DT.Union (desugar_union_type None u)
  | ST.Record r ->
      desugar_record_type [] r
  | ST.App(ST.Ctor l, t) ->
      DT.Union((), [(l, desugar_type t)], None)
  | ST.RowRest v ->
      DT.Union((), [], Some v)
  | _ ->
      failwith "TODO"
and desugar_q_type q vars body =
  let rec go = function
    | [] -> desugar_type body
    | (x :: xs) -> DT.Quant((), q, x, DK.Unknown, go xs)
  in
  go vars
and desugar_union_type tail (l, r) =
  match desugar_type l, desugar_type r, tail with
  | DT.Union((), lbls_l, None), DT.Union((), lbls_r, None), (Some v)
  | DT.Union((), lbls_l, None), DT.Union((), lbls_r, Some v), None
  | DT.Union((), lbls_l, Some v), DT.Union((), lbls_r, None), None ->
      ((), lbls_l @ lbls_r, Some v)
  | DT.Union((), lbls_l, None), DT.Union((), lbls_r, None), None ->
      ((), lbls_l @ lbls_r, None)
  | _ -> raise
    (MuleErr.MuleExn
      (MuleErr.MalformedType
        "Unions must be composed of ctors and at most one ...r"))
and desugar_record_type fields = function
  | (ST.Type _ :: fs) ->
      (* TODO: do something with this. *)
      desugar_record_type fields fs
  | [] ->
      DT.Record((), fields, None)
  | [ST.Rest v] ->
      DT.Record((), fields, Some v)
  | (ST.Field (l, t) :: rest) ->
      desugar_record_type ((l, desugar_type t)::fields) rest
  | (ST.Rest _ :: _) -> raise
    (MuleErr.MuleExn
      (MuleErr.MalformedType "row variable before the end of a record type."))


let rec desugar = function
  | S.Integer n -> D.Integer n
  | S.Var v -> D.Var v
  | S.App (f, x) -> D.App (desugar f, desugar x)
  | S.Lam (SP.Var v :: pats, body) ->
      D.Lam(v, desugar (S.Lam (pats, body)))
  | S.Lam ((SP.Annotated (SP.Var v, ty) :: pats), body) ->
      let v' = Gensym.anon_var () in
      D.Lam
        ( v'
        , D.Let
          ( v
          , D.App(D.WithType (desugar_type ty), D.Var v')
          , desugar (S.Lam (pats, body))
          )
        )
  | S.Lam ((SP.Integer _) as p :: _, _) ->
      incomplete_pattern p
  | S.Lam (pat :: pats, body) ->
      let var = Gensym.anon_var () in
      D.Lam
        ( var
        , desugar
            (S.Match
              ( S.Var var
              , [ (pat
                  , S.Lam (pats, body)
                  )
                ]
              )
            )
        )
  | S.Lam ([], body) -> desugar body
  | S.Record [] -> D.EmptyRecord
  | S.Record fields -> desugar_record fields
  | S.Update(e, []) ->
      desugar e
  | S.Update(e, (`Value (l, _, v)::fs)) ->
      D.App(D.App(D.Update l, (desugar (S.Update(e, fs)))), desugar v)
  | S.Update(e, (`Type _ :: fs)) ->
      (* TODO: do something with this. *)
      desugar (S.Update(e, fs))
  | S.GetField (e, l) ->
      D.App(D.GetField(`Strict, l), desugar e)
  | S.Ctor label ->
      (* The choice of variable name here doesn't matter, since
       * there's nothing we need to worry about shadowing. *)
      let param = Ast.Var.of_string "x" in
      D.Lam (param, D.Ctor (label, D.Var param))
  | S.Match (e, cases) ->
      D.App
        ( desugar_lbl_match LabelMap.empty cases
        , desugar e
        )
  | S.Let((SP.Integer _) as p, _, _) ->
      incomplete_pattern p
  | S.Let(SP.Wild, e, body) ->
      desugar (S.Let(SP.Var (Gensym.anon_var ()), e, body))
  | S.Let(SP.Annotated(pat, ty), e, body) ->
      desugar (S.Let(pat, S.WithType(e, ty), body))
  | S.Let(SP.Ctor(lbl, pat), e, body) ->
      let v = Gensym.anon_var () in
      desugar (S.Match(e, [(SP.Ctor(lbl, SP.Var v), S.Let(pat, S.Var v, body))]))
  | S.Let(SP.Var v, e, body) ->
      D.Let(v, D.App(D.Fix `Let, D.Lam(v, desugar e)), desugar body)
  | S.WithType(e, ty) ->
      D.App(D.WithType(desugar_type ty), desugar e)
and desugar_record fields =
  let record_var = Gensym.anon_var () in
  let get_record_field lbl =
    D.App(D.GetField(`Lazy, lbl), D.Var record_var)
  in
  let label_map =
    List.filter_map fields ~f:(function
      | `Value (l, ty, _) ->
          Some (l, ty)
      | `Type _ -> None)
    |> Map.of_alist_exn (module Ast.Label)
  in
  let rec subst env expr = match expr with
    | D.Integer n -> D.Integer n
    | D.Var v ->
        let lbl = var_to_lbl v in
        begin match Map.find env lbl with
        | None -> D.Var v
        | Some None -> get_record_field lbl
        | Some (Some ty) ->
            D.App(D.WithType(desugar_type ty), get_record_field lbl)
        end
    | D.Ctor(lbl, body) ->
        D.Ctor(lbl, subst env body)
    | D.Lam (v, body) ->
        D.Lam
          ( v
          , subst
              (Map.remove env (var_to_lbl v))
              body
          )
    | D.App(f, x) ->
        D.App(subst env f, subst env x)
    | D.Match {cases; default} ->
        D.Match
          { cases =
              Map.map cases ~f:(fun (var, body) ->
                let env' = Map.remove env (var_to_lbl var) in
                ( var
                , subst env' body
                )
              )
          ; default = Option.map default ~f:(function
              | (None, body) -> (None, subst env body)
              | (Some var, body) ->
                  ( Some var
                  , let env' = Map.remove env (var_to_lbl var) in
                    subst env' body
                  )
            )
          }
    | D.Let(v, e, body) ->
        D.Let
          ( v
          , subst env e
          , subst (Map.remove env (var_to_lbl v)) body
          )
    | D.Fix _ | D.EmptyRecord | D.GetField _ | D.Update _ | D.WithType _ ->
        expr
  in
  let rec build_record = function
    | [] -> D.EmptyRecord
    | `Value(l, ty, v) :: fs ->
        let v' =
          begin match ty with
          | None -> v
          | Some ty' -> S.WithType(v, ty')
          end
        in
        D.App
          ( D.App
            ( D.Update l
            , build_record fs
            )
          , subst label_map (desugar v')
          )
    | `Type _ :: fs ->
        (* TODO: do something with this. *)
        build_record fs
  in
  D.App(D.Fix `Record, D.Lam(record_var, build_record fields))
and desugar_lbl_match dict = function
  | [] -> D.Match
      { default = None
      ; cases = finalize_dict dict
      }
  | [(SP.Wild, body)] -> D.Match
      { default = Some (None, desugar body)
      ; cases = finalize_dict dict
      }
  | [(SP.Var v, body)] -> D.Match
      { default = Some (Some v, desugar body)
      ; cases = finalize_dict dict
      }
  | [(SP.Annotated (SP.Var v, ty), body)] ->
      let v' = Gensym.anon_var () in
      let let_ = D.Let
        ( v
        , D.App(D.WithType(desugar_type ty), D.Var v')
        , desugar body
        )
      in
      D.Match
        { default = Some(Some v', let_)
        ; cases = finalize_dict dict
        }
  | (SP.Ctor (lbl, p), body) :: cases ->
      let dict' =
          Map.update dict lbl ~f:(function
            | None -> [(p, body)]
            | Some cases -> ((p, body) :: cases)
          )
      in
      desugar_lbl_match dict' cases
  | (SP.Annotated (p, _), body) :: cases ->
      (* TODO: we'll want to actually do something with these eventually.
       * Maybe the thing to do is just only allow annotations on pattern variables,
       * rather than arbitrary patterns? *)
      desugar_lbl_match dict ((p, body) :: cases)
  | (_ :: _) ->
      raise MuleErr.(MuleExn UnreachableCases)
and finalize_dict dict =
  Map.map dict
    ~f:( fun cases ->
      let v = Gensym.anon_var () in
      ( v
      , D.App
          ( desugar_lbl_match LabelMap.empty (List.rev cases)
          , D.Var v
          )
      )
    )

let desugar e =
  try Ok (desugar e)
  with MuleErr.MuleExn err -> Error err
