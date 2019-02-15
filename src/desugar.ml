
module SP = Ast.Surface.Pattern
module S = Ast.Surface.Expr
module D = Ast.Desugared.Expr
module RowMap = Ast.Desugared.RowMap

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
  | S.Record fields ->
      D.Record (
        fields
        |> List.to_seq
        |> Seq.map (fun (l, e) -> (l, desugar e))
        |> RowMap.of_seq
      )
  | S.Update(e, fields) ->
      D.Update
        ( desugar e
        , List.map (fun (l, v) -> (l, desugar v)) fields
        )
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

let desugar e =
  try OrErr.Ok (desugar e)
  with Error.MuleExn err -> OrErr.Err err
