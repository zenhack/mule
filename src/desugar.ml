
module SP = Ast.Surface.Pattern
module S = Ast.Surface.Expr
module ST = Ast.Surface.Type
module D = Ast.Desugared.Expr
module DT = Ast.Desugared.Type
module RowMap = Ast.Desugared.RowMap

module VSet = Set.Make(Ast.Var)

let rec free_vars: D.t -> VSet.t = function
  | D.Lam(param, body) ->
      free_vars body
      |> VSet.remove param
  | D.Match {cases; default} ->
      let def_fvs = match default with
        | None -> VSet.empty
        | Some (None, e) -> free_vars e
        | Some (Some v, e) -> free_vars (D.Lam(v, e))
      in
      RowMap.fold
        (fun _key -> VSet.union)
        (RowMap.map
          (fun (param, body) -> free_vars (D.Lam (param, body)))
          cases)
        VSet.empty
      |> VSet.union def_fvs
  | D.App(f, x) ->
      VSet.union (free_vars f) (free_vars x)
  | D.EmptyRecord ->
      VSet.empty
  | D.GetField(e, _) ->
      free_vars e
  | D.Update(e, _l, field) ->
      VSet.union (free_vars e) (free_vars field)
  | D.Ctor(_l, e) ->
      free_vars e
  | D.Var v ->
      VSet.singleton v
  | D.WithType(e, _ty) ->
      free_vars e
  | D.Let(v, e, body) ->
      VSet.union
        (free_vars e)
        (VSet.remove v (free_vars body))

let rec desugar_type = function
  | ST.Fn(param, ret) ->
      DT.Fn((), desugar_type param, desugar_type ret)
  | ST.All([], body) ->
      desugar_type body
  | ST.All(v::vs, body) ->
      DT.All((), v, desugar_type (ST.All(vs, body)))
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
and desugar_union_type tail (l, r) =
  match desugar_type l, desugar_type r, tail with
  | DT.Union((), lbls_l, None), DT.Union((), lbls_r, None), (Some v)
  | DT.Union((), lbls_l, None), DT.Union((), lbls_r, Some v), None
  | DT.Union((), lbls_l, Some v), DT.Union((), lbls_r, None), None ->
      ((), lbls_l @ lbls_r, Some v)
  | DT.Union((), lbls_l, None), DT.Union((), lbls_r, None), None ->
      ((), lbls_l @ lbls_r, None)
  | _ -> raise
    (Error.MuleExn
      (Error.MalformedType
        "Unions must be composed of ctors and at most one ...r"))
and desugar_record_type fields = function
  | [] ->
      DT.Record((), fields, None)
  | [ST.Rest v] ->
      DT.Record((), fields, Some v)
  | (ST.Field (l, t) :: rest) ->
      desugar_record_type ((l, desugar_type t)::fields) rest
  | (ST.Rest _ :: _) -> raise
    (Error.MuleExn
      (Error.MalformedType "row variable before the end of a record type."))


let rec desugar = function
  | S.Var v -> D.Var v
  | S.App (f, x) -> D.App (desugar f, desugar x)
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
  | S.Record [] ->
      D.EmptyRecord
  | S.Record ((l, v)::fs) ->
      D.Update(desugar (S.Record fs), l, desugar v)
  | S.Update(e, []) ->
      desugar e
  | S.Update(e, ((l, v)::fs)) ->
      D.Update (desugar (S.Update(e, fs)), l, desugar v)
  | S.GetField (e, l) ->
      D.GetField (desugar e, l)
  | S.Ctor label ->
      (* The choice of variable name here doesn't matter, since
       * there's nothing we need to worry about shadowing. *)
      let param = Ast.Var.of_string "x" in
      D.Lam (param, D.Ctor (label, D.Var param))
  | S.Match (e, cases) ->
      D.App
        ( desugar_match RowMap.empty cases
        , desugar e
        )
  | S.Let(SP.Var v, e, body) ->
      D.Let (v, desugar e, desugar body)
  | S.Let(pat, e, body) ->
      (* TODO: rework with so it stays a let binding; otherwise it won't generalize inner
       * variables. *)
      desugar (S.Match(e, [(pat, body)]))
and desugar_match dict = function
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
        , D.WithType(D.Var v', desugar_type ty)
        , desugar body
        )
      in
      D.Match
        { default = Some(Some v', let_)
        ; cases = finalize_dict dict
        }
  | (SP.Ctor (lbl, p), body) :: cases ->
      let dict' =
          RowMap.update
            lbl
            (function
              | None -> Some [(p, body)]
              | Some cases -> Some ((p, body) :: cases)
            )
            dict
      in
      desugar_match dict' cases
  | (SP.Annotated (p, _), body) :: cases ->
      (* TODO: we'll want to actually do something with these eventually *)
      desugar_match dict ((p, body) :: cases)
  | (_ :: _) ->
      raise (Error.MuleExn Error.UnreachableCases)
and finalize_dict dict =
  RowMap.map
    ( fun cases ->
      let v = Gensym.anon_var () in
      ( v
      , D.App
          ( desugar_match RowMap.empty (List.rev cases)
          , D.Var v
          )
      )
    )
    dict

let rec simplify e = match e with
  | D.Lam (param, body) ->
      begin match simplify body with
        | D.App(f, D.Var v) when
            Ast.Var.equal v param
            && not (VSet.mem param (free_vars f)) ->
              f
        | b -> D.Lam(param, b)
      end
  | D.Match {cases; default = Some (Some param, body)}
      when RowMap.is_empty cases ->
        simplify (D.Lam(param, body))
  | D.App(f, x) ->
      begin match D.App(simplify f, simplify x) with
        | D.App (D.Lam(p, D.Ctor(c, D.Var v)), arg) when Ast.Var.equal v p ->
            D.Ctor(c, arg)
        | e' -> e'
      end
  | D.GetField (e, f) ->
      D.GetField(simplify e, f)
  | D.EmptyRecord ->
      D.EmptyRecord
  | D.Update (e', lbl, field) ->
      D.Update
        ( simplify e'
        , lbl
        , simplify field
        )
  | D.Ctor (l, e') ->
      D.Ctor(l, simplify e')
  | D.Var _ | D.Match _ ->
      e (* TODO: don't be lazy about match. *)
  | D.WithType (e', ty) ->
      D.WithType(simplify e', ty)
  | D.Let(v, e', body) ->
      D.Let (v, simplify e', simplify body)

let desugar e =
  try OrErr.Ok (simplify (desugar e))
  with Error.MuleExn err -> OrErr.Err err
