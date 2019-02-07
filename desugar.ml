
module SP = Ast.Surface.Pattern
module S = Ast.Surface.Expr
module D = Ast.Desugared.Expr
module RowMap = Ast.Desugared.RowMap

let rec desugar = function
  | S.Var(_, v) -> D.Var v
  | S.App (_, f, x) -> D.App (desugar f, desugar x)
  | S.Lam (_, param, body) -> D.Lam (param, desugar body)
  | S.Record (_, fields) ->
      D.Record (
        fields
        |> List.to_seq
        |> Seq.map (fun (l, e) -> (l, desugar e))
        |> RowMap.of_seq
      )
  | S.Update(_, e, fields) ->
      D.Extend
        ( desugar e
        , List.map (fun (l, v) -> (l, desugar v)) fields
        )
  | S.GetField (_, e, l) ->
      D.GetField (desugar e, l)
  | S.Ctor (_, label) ->
      (* The choice of variable name here doesn't matter, since
       * there's nothing we need to worry about shadowing. *)
      let param = Ast.Var "x" in
      D.Lam (param, D.Ctor (label, D.Var param))
  | S.Match (_, e, cases) ->
      D.App
        ( desugar_match RowMap.empty cases
        , desugar e
        )
and desugar_match dict = function
  | [] -> D.Match
      { default = None
      ; cases = finalize_dict dict
      }
  | [(SP.Wild _, body)] -> D.Match
      { default = Some (None, desugar body)
      ; cases = finalize_dict dict
      }
  | [(SP.Var (_, v), body)] -> D.Match
      { default = Some (Some v, desugar body)
      ; cases = finalize_dict dict
      }
  | (SP.Ctor (_, lbl, p), body) :: cases ->
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
  | (_ :: _) ->
      (* We have something other than a ctor that has more patterns
       * after it. This should have been caught earlier in the pipeline.
       *)
      Debug.impossible "unreachable cases."
and finalize_dict dict =
  RowMap.map
    ( fun cases ->
      let v = Ast.Var ("-" ^ string_of_int (Gensym.gensym())) in
      ( v
      , D.App
          ( desugar_match RowMap.empty (List.rev cases)
          , D.Var v
          )
      )
    )
    dict
