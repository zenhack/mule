include Typecheck_t

module DE = Desugared_ast_expr
module GT = Graph_types

let typecheck ctx ~get_import_type:_ ~want:_ ~export:_ exp =
  (* TODO: rather than just throwing this away here, rework the
     interfaces so that gen_expr and our callers agree. *)
  let exp = DE.map exp ~f:(fun _ -> ()) in
  let g = Gen_constraints.Gen.gen_expr ctx exp in
  let q = Lazy.force (GT.GNode.get g) in
  Solve.solve ctx;
  match Context.errors ctx with
  | [] -> q
  | (e :: _es) ->
      (* TODO: report all errors, not just the first. *)
      MuleErr.throw e
