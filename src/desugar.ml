module SP = Ast.Surface.Pattern
module S = Ast.Surface.Expr
module ST = Ast.Surface.Type
module D = Ast.Desugared.Expr
module DT = Ast.Desugared.Type
module DK = Ast.Desugared.Kind

let rec free_vars: D.t -> VarSet.t = function
  | D.Lam(param, body) ->
      Set.remove (free_vars body) param
  | D.Match {cases; default} ->
      let def_fvs = match default with
        | None -> Set.empty (module Ast.Var)
        | Some (None, e) -> free_vars e
        | Some (Some v, e) -> free_vars (D.Lam(v, e))
      in
      Map.map cases ~f:(fun (param, body) -> free_vars (D.Lam (param, body)))
      |> Map.fold
          ~init:(Set.empty (module Ast.Var))
          ~f:(fun ~key:_ ~data -> Set.union data)
      |> Set.union def_fvs
  | D.App(f, x) ->
      Set.union (free_vars f) (free_vars x)
  | D.EmptyRecord | D.GetField _ | D.Update _ ->
      Set.empty (module Ast.Var)
  | D.Ctor(_l, e) ->
      free_vars e
  | D.Var v ->
      Set.singleton (module Ast.Var) v
  | D.WithType _ ->
      Set.empty (module Ast.Var)
  | D.Let(v, e, body) ->
      Set.union
        (free_vars e)
        (Set.remove (free_vars body) v)

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
      D.App(D.App(D.Update l, desugar (S.Record fs)), desugar v)
  | S.Update(e, []) ->
      desugar e
  | S.Update(e, ((l, v)::fs)) ->
      D.App(D.App(D.Update l, (desugar (S.Update(e, fs)))), desugar v)
  | S.GetField (e, l) ->
      D.App(D.GetField l, desugar e)
  | S.Ctor label ->
      (* The choice of variable name here doesn't matter, since
       * there's nothing we need to worry about shadowing. *)
      let param = Ast.Var.of_string "x" in
      D.Lam (param, D.Ctor (label, D.Var param))
  | S.Match (e, cases) ->
      D.App
        ( desugar_match (Map.empty (module Ast.Label)) cases
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
      desugar_match dict' cases
  | (SP.Annotated (p, _), body) :: cases ->
      (* TODO: we'll want to actually do something with these eventually *)
      desugar_match dict ((p, body) :: cases)
  | (_ :: _) ->
      raise MuleErr.(MuleExn UnreachableCases)
and finalize_dict dict =
  Map.map dict
    ~f:( fun cases ->
      let v = Gensym.anon_var () in
      ( v
      , D.App
          ( desugar_match (Map.empty (module Ast.Label)) (List.rev cases)
          , D.Var v
          )
      )
    )

let rec simplify e = match e with
  | D.Lam (param, body) ->
      begin match simplify body with
        | D.App(f, D.Var v) when
            Ast.Var.equal v param
            && not (Set.mem (free_vars f) param) ->
              f
        | b -> D.Lam(param, b)
      end
  | D.Match {cases; default = Some (Some param, body)}
      when Map.is_empty cases ->
        simplify (D.Lam(param, body))
  | D.App(f, x) ->
      begin match D.App(simplify f, simplify x) with
        | D.App (D.Lam(p, D.Ctor(c, D.Var v)), arg) when Ast.Var.equal v p ->
            D.Ctor(c, arg)
        | e' -> e'
      end
  | D.GetField lbl ->
      D.GetField lbl
  | D.EmptyRecord ->
      D.EmptyRecord
  | D.Update lbl ->
      D.Update lbl
  | D.Ctor (l, e') ->
      D.Ctor(l, simplify e')
  | D.Var _ | D.Match _ ->
      e (* TODO: don't be lazy about match. *)
  | D.WithType ty ->
      D.WithType ty
  | D.Let(v, e', body) ->
      D.Let (v, simplify e', simplify body)

let desugar e =
  try Ok (simplify (desugar e))
  with MuleErr.MuleExn err -> Error err
