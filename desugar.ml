
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
